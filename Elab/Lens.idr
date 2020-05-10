module Elab.Lens

import public Core.TT.Lens
import public Core.Globals

import Core.TT
import Core.Pattern
import Core.Clause

import Decidable.Equality

mutual
  mlBnd : Applicative t => {n : Nat} -> ((n : Nat) -> MetaNum -> t (TT q n)) -> (Binding q n) -> t (Binding q n)
  mlBnd f (B n q ty) = B n q <$> mlTm f ty

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
