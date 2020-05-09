module Inference.Elab

import public Core.Globals

import Core.TC
import Control.Monad.State

%default total
%undotted_record_projections off

public export
data Error
  = NotImplementedYet
  | OtherError String

export
Show Error where
  show NotImplementedYet = "not implemented yet"
  show (OtherError msg) = "error: " ++ msg

record Equality (q : Type) where
  constructor MkE
  {0 n : Nat}
  lhs : TT q n
  rhs : TT q n

TC : Type -> Nat -> Type -> Type
TC q n a = Core.TC.TC Error (List (Equality q)) q n a

fresh : State Int Int
fresh = do
  i <- get
  put (i+1)
  pure i

mutual
  nrBnd : Binding q n -> State Int (Binding q n)
  nrBnd (B n q ty) = B n q <$> nrTm ty

  nrTm : TT q n -> State Int (TT q n)
  nrTm (P gn) = pure $ P gn
  nrTm (V i) = pure $ V i
  nrTm (Lam b rhs) = Lam <$> nrBnd b <*> nrTm rhs
  nrTm (Pi b rhs) = Pi <$> nrBnd b <*> nrTm rhs
  nrTm (App q f x) = App q <$> nrTm f <*> nrTm x
  nrTm Type_ = pure Type_
  nrTm Erased = pure Erased

mutual
  nrPat : Pat q n -> State Int (Pat q n)
  nrPat (PV pv) = pure $ PV pv
  nrPat (PCtorApp f args) = PCtorApp f <$> traverse nrQPat args
  nrPat (PForced tm) = PForced <$> nrTm tm
  nrPat PWildcard = pure PWildcard

  nrQPat : (q, Pat q n) -> State Int (q, Pat q n)
  nrQPat (q, pat) = do
    pat' <- nrPat pat
    pure (q, pat')

nrCtx : Context q n -> State Int (Context q n)
nrCtx [] = pure []
nrCtx (b :: bs) = [| nrBnd b :: nrCtx bs |]

nrClause : Clause q argn -> State Int (Clause q argn)
nrClause (MkClause pi lhs rhs) =
  MkClause <$> nrCtx pi <*> traverse nrQPat lhs <*> nrTm rhs

nrBody : Body q -> State Int (Body q)
nrBody Postulate = pure Postulate
nrBody (Constructor arity) = pure $ Constructor arity
nrBody (Foreign code) = pure $ Foreign code
nrBody (Clauses argn cs) = Clauses argn <$> traverse nrClause cs

nrDef : Definition q -> State Int (Definition q)
nrDef (MkDef b body) = MkDef <$> nrBnd b <*> nrBody body

nrGlobals : Globals q -> State Int (Globals q)
nrGlobals = map fromBlocks . traverse (traverse nrDef) . toBlocks

export
elab : Globals q -> Either Error (Globals q)
elab gs = ?rhs
