module Elab.Lens

import public Core.TT.Lens
import public Core.Globals

import Core.TT
import Core.Pattern
import Core.Clause

import Decidable.Equality

public export
MetaLens : Type -> Type -> Type
MetaLens q a = Traversal a a MetaNum (Either MetaNum (n ** TT q n))

mutual
  mlBnd : {n : Nat} -> MetaLens q (Binding q n)
  mlBnd f (B n q ty) = B n q <$> mlTm f ty

  mlTm : {n : Nat} -> MetaLens q (TT q n)
  mlTm f (P gn) = pure $ P gn
  mlTm f (V i) = pure $ V i
  mlTm f (Lam b rhs) = Lam <$> mlBnd f b <*> mlTm f rhs
  mlTm f (Pi b rhs) = Pi <$> mlBnd f b <*> mlTm f rhs
  mlTm f (App q g x) = App q <$> mlTm f g <*> mlTm f x
  mlTm f Type_ = pure Type_
  mlTm f Erased = pure Erased
  mlTm f (Meta i) = f i <&> \case
    Left j => Meta j
    Right (n' ** tm) => case decEq n n' of
      Yes Refl => tm
      No  _    => Meta i

mutual
  mlPat : {n : Nat} -> MetaLens q (Pat q n)
  mlPat f (PV pv) = pure $ PV pv
  mlPat f (PCtorApp g args) = PCtorApp g <$> traverse (mlQPat f) args
  mlPat f (PForced tm) = PForced <$> mlTm f tm
  mlPat f PWildcard = pure PWildcard

  mlQPat : {n : Nat} -> MetaLens q (q, Pat q n)
  mlQPat f (q, pat) = (\pat' => (q, pat')) <$> mlPat f pat

mlCtx : {n : Nat} -> MetaLens q (Context q n)
mlCtx f [] = pure []
mlCtx f (b :: bs) = [| mlBnd f b :: mlCtx f bs |]

mlClause : MetaLens q (Clause q argn)
mlClause f (MkClause pi lhs rhs) =
  MkClause <$> mlCtx f pi <*> traverse (mlQPat f) lhs <*> mlTm f rhs

mlBody : MetaLens q (Body q)
mlBody f Postulate = pure Postulate
mlBody f (Constructor arity) = pure $ Constructor arity
mlBody f (Foreign code) = pure $ Foreign code
mlBody f (Clauses argn cs) = Clauses argn <$> traverse (mlClause f) cs

mlDef : MetaLens q (Definition q)
mlDef f (MkDef b body) = MkDef <$> mlBnd f b <*> mlBody f body

export
mlGlobals : MetaLens q (Globals q)
mlGlobals f = map fromBlocks . traverse (traverse (mlDef f)) . toBlocks
