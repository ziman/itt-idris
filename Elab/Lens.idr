module Elab.Lens

import public Core.TT.Lens
import public Core.Globals
import public Data.SortedMap

import Core.TT
import Core.TT.Lens
import Core.Pattern
import Core.Clause

import Data.Maybe
import Decidable.Equality
import Control.Monad.Identity

mutual
  mlBnd : Applicative t => {n : Nat} -> ((n : Nat) -> MetaNum -> t (TT q n)) -> (Binding q n) -> t (Binding q n)
  mlBnd f (B n q ty) = B n q <$> mlTm f ty

  export
  mlTm : Applicative t => {n : Nat} -> ((n : Nat) -> MetaNum -> t (TT q n)) -> (TT q n) -> t (TT q n)
  mlTm f (P gn) = pure $ P gn
  mlTm f (V i) = pure $ V i
  mlTm f (Lam b rhs) = Lam <$> mlBnd f b <*> mlTm f rhs
  mlTm f (Pi b rhs) = Pi <$> mlBnd f b <*> mlTm f rhs
  mlTm f (App q g x) = App q <$> mlTm f g <*> mlTm f x
  mlTm f Type_ = pure Type_
  mlTm f Erased = pure Erased
  mlTm f (Meta i) = f _ i

mutual
  mlPat : Applicative t => {n : Nat} -> ((n : Nat) -> MetaNum -> t (TT q n)) -> (Pat q n) -> t (Pat q n)
  mlPat f (PV pv) = pure $ PV pv
  mlPat f (PCtorApp g args) = PCtorApp g <$> traverse (mlQPat f) args
  mlPat f (PForced tm) = PForced <$> mlTm f tm
  mlPat f PWildcard = pure PWildcard

  mlQPat : Applicative t => {n : Nat} -> ((n : Nat) -> MetaNum -> t (TT q n)) -> (q, Pat q n) -> t (q, Pat q n)
  mlQPat f (q, pat) = (\pat' => (q, pat')) <$> mlPat f pat

mlCtx : Applicative t => {n : Nat} -> ((n : Nat) -> MetaNum -> t (TT q n)) -> (Context q n) -> t (Context q n)
mlCtx f [] = pure []
mlCtx f (b :: bs) = [| mlBnd f b :: mlCtx f bs |]

mlClause : Applicative t => ((n : Nat) -> MetaNum -> t (TT q n)) -> (Clause q argn) -> t (Clause q argn)
mlClause f (MkClause pi lhs rhs) =
  MkClause <$> mlCtx f pi <*> traverse (mlQPat f) lhs <*> mlTm f rhs

mlBody : Applicative t => ((n : Nat) -> MetaNum -> t (TT q n)) -> (Body q) -> t (Body q)
mlBody f Postulate = pure Postulate
mlBody f (Constructor arity) = pure $ Constructor arity
mlBody f (Foreign code) = pure $ Foreign code
mlBody f (Clauses argn cs) = Clauses argn <$> traverse (mlClause f) cs

mlDef : Applicative t => ((n : Nat) -> MetaNum -> t (TT q n)) -> (Definition q) -> t (Definition q)
mlDef f (MkDef b body) = MkDef <$> mlBnd f b <*> mlBody f body

export
mlGlobals : Applicative t => ((n : Nat) -> MetaNum -> t (TT q n)) -> (Globals q) -> t (Globals q)
mlGlobals f = map fromBlocks . traverse (traverse (mlDef f)) . toBlocks

export
subst :
    (trav : (f : (n : Nat) -> MetaNum -> Identity (TT q n)) -> a -> Identity a)
    -> MetaNum -> (n : Nat) -> TT q n
    -> a -> a
subst {a} trav mn n tm rhs = runIdentity $ trav f rhs
  where
    f : (n' : Nat) -> (mn' : MetaNum) -> Identity (TT q n')
    f n' mn' = pure $ case (decEq n n', decEq mn mn') of
      (Yes Refl, Yes Refl) => tm
      _ => Meta mn'

public export
Subst : Type -> Type
Subst q = SortedMap MetaNum (n ** TT q n)

export
substOne :
    (trav : (f : (n : Nat) -> MetaNum -> Identity (TT q n)) -> a -> Identity a)
    -> MetaNum -> (n' ** TT q n')
    -> a -> a
substOne trav mn' (n' ** tm') tm = runIdentity $ trav f tm
  where
    f : (n : Nat) -> MetaNum -> Identity (TT q n)
    f n mn = pure $
      if mn == mn'
        then fromMaybe (Meta mn) (rescope ttVars tm')
        else Meta mn  -- don't do anything

export
substMany :
    (trav : (f : (n : Nat) -> MetaNum -> Identity (TT q n)) -> a -> Identity a)
    -> Subst q -> a -> a
substMany trav s tm = runIdentity $ trav f tm
  where
    f : (n : Nat) -> MetaNum -> Identity (TT q n)
    f n mn = pure $ case lookup mn s of
      Nothing => Meta mn
      Just (n' ** tm') => fromMaybe (Meta mn) (rescope ttVars tm')
