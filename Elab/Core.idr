module Elab.Core

import public Core.Globals

import Core.TC
import Core.Normalise
import Elab.Lens

import Data.List
import Control.Monad.State

%default total
%undotted_record_projections off

public export
data Error
  = NotImplementedYet
  | OtherError String
  | EvalError Normalise.EvalError

export
Show Error where
  show NotImplementedYet = "not implemented yet"
  show (OtherError msg) = "error: " ++ msg
  show (EvalError e) = show e

TC.Error Error where
  fromEvalError = EvalError

data Certainty = Certain | Uncertain

Semigroup Certainty where
  Certain <+> Certain = Certain
  _ <+> _ = Uncertain

record Equality (q : Type) where
  constructor MkE
  {0 n : Nat}
  certainty : Certainty
  lhs : TT q n
  rhs : TT q n

TC : Type -> Nat -> Type -> Type
TC q n a = TC Error (List (Equality q)) q n a


mutual
  infix 3 ~=
  (~=) : TT q n -> TT q n -> TC q n ()
  lhs ~= rhs = do
    lhsWHNF <- redTC WHNF lhs
    rhsWHNF <- redTC WHNF rhs
    conv lhsWHNF rhsWHNF

  conv : TT q n -> TT q n -> TC q n ()
  conv lhs rhs = ?rhs_conv

mutual
  eqsBnd : Binding q n -> TC q n ()
  eqsBnd (B n q ty) = do
    tyTy <- eqsTm ty
    tyTy ~= Type_

  eqsTm : TT q n -> TC q n (TT q n)
  eqsTm tm = ?rhs_eqsTy

mutual
  eqsPat : Pat q n -> TC q n (TT q n)
  eqsPat pat = ?rhs_eqsPat

  eqsPatApp : TT q n -> List (q, Pat q n) -> TC q n (TT q n)
  eqsPatApp fty [] = pure fty
  eqsPatApp fty ((q,x) :: xs) = do
    xTy <- eqsPat x
    redTC WHNF fty >>= \case
      Pi (B piN piQ piTy) piRhs => do
        piTy ~= xTy
        eqsPatApp (subst (substFZ $ patToTm x) piRhs) xs

eqsCtx : Context q n -> TC q Z ()
eqsCtx [] = pure ()
eqsCtx (b :: bs) = do
  eqsCtx bs
  withCtx bs $ eqsBnd b

eqsClause : Binding q Z -> Clause q argn -> TC q Z ()
eqsClause fbnd (MkClause pi lhs rhs) = do
  eqsCtx pi
  withCtx pi $ do
    lhsTy <- eqsPatApp (weakenClosed fbnd.type) (toList lhs)
    rhsTy <- eqsTm rhs
    lhsTy ~= rhsTy

eqsBody : Binding q Z -> Body q -> TC q Z ()
eqsBody fbnd Postulate = pure ()
eqsBody fbnd (Constructor arity) = pure ()
eqsBody fbnd (Foreign code) = pure ()
eqsBody fbnd (Clauses argn cs) = traverse_ (eqsClause fbnd) cs

eqsDef : Definition q -> TC q Z ()
eqsDef (MkDef b body) = do
  eqsBnd b
  eqsBody b body

eqsGlobals : TC q Z ()
eqsGlobals = do
  gs <- getGlobals
  traverse_ (traverse_ eqsDef) $ toBlocks gs

numberMetas : Globals q -> Globals q
numberMetas gs = evalState (mlGlobals numberMeta gs) 0
  where
    numberMeta : Int -> State Int (Either Int (n ** TT q n))
    numberMeta _ = do
      i <- get
      put (i+1)
      pure $ Left i

export
elab : Globals q -> Either Error (Globals q)
elab gs = ?rhsElab
