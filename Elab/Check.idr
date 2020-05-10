module Elab.Check

import public Elab.Equality
import public Core.TC
import public Core.Globals
import public Core.Quantity

import Core.TT
import Core.TT.Pretty
import Core.Normalise
import Elab.Lens
import Utils.Pretty

import Data.List
import Control.Monad.State

%default total
%undotted_record_projections off

public export
data Error
  = NotImplementedYet
  | OtherError String
  | TCError TCError
  | NotPi Doc
  | CantInferWildcard
  | CantInfer Doc
  | CantConvert Doc Doc
  | QuantityMismatch Q Q

export
Show Error where
  show NotImplementedYet = "not implemented yet"
  show (OtherError msg) = "error: " ++ msg
  show (TCError e) = show e
  show (NotPi ty) = "not a pi type:" ++ show ty
  show CantInferWildcard = "can't infer _"
  show (CantInfer tm) = "can't infer: " ++ show tm
  show (CantConvert lhs rhs) = "can't convert " ++ show lhs ++ " with " ++ show rhs

TC.Error Error where
  tcError = TCError

TC : Nat -> Type -> Type
TC n a = TC Error (List Equality) (Maybe Q) n a

Term : Nat -> Type
Term = TT (Maybe Q)

Ty : Nat -> Type
Ty = TT (Maybe Q)

cantConvert : Term n -> Term n -> TC n a
cantConvert lhs rhs = do
  lhsD <- prettyCtx lhs
  rhsD <- prettyCtx rhs
  throw $ CantConvert lhsD rhsD

infix 3 ~~
(~~) : Maybe Q -> Maybe Q -> TC n ()
Just q ~~ Just q' =
  if q == q'
    then pure ()
    else throw $ QuantityMismatch q q'
_ ~~ _ = pure ()

mutual
  infix 3 ~=
  (~=) : Term n -> Term n -> Certainty -> TC n ()
  (lhs ~= rhs) c = do
    lhsWHNF <- redTC WHNF lhs
    rhsWHNF <- redTC WHNF rhs
    conv c lhsWHNF rhsWHNF

  conv : Certainty -> Term n -> Term n -> TC n ()
  conv c (V i) (V j) =
    if i == j
      then pure ()
      else cantConvert (V i) (V j)
  conv c (P n) (P n') =
    if n == n'
      then pure ()
      else cantConvert (P n) (P n')
  conv c (Lam b@(B n q ty) rhs) (Lam (B n' q' ty') rhs') = do
    q ~~ q'
    (ty ~= ty') c
    withBnd b $
      (rhs ~= rhs') c
  conv c (Pi b@(B n q ty) rhs) (Pi (B n' q' ty') rhs') = do
    q ~~ q'
    (ty ~= ty') c
    withBnd b $
      (rhs ~= rhs') c
  conv c (App Nothing f x) (App Nothing f' x') = do
    (f ~= f') c
    (x ~= x') Uncertain
  conv c (App (Just I) f x) (App (Just I) f' x') = do
    (f ~= f') c
  conv c (App (Just q) f x) (App (Just q') f' x') = do
    Just q ~~ Just q'
    (f ~= f') c
    (x ~= x') c
  conv c Type_ Type_ = pure ()
  conv c (Meta i) tm = do
    ctx <- getCtx
    emit [MkE c ctx (Meta i) tm]
  conv c tm (Meta i) = do
    ctx <- getCtx
    emit [MkE c ctx (Meta i) tm]
  conv c lhs rhs = cantConvert lhs rhs

mutual
  eqsBnd : Binding (Maybe Q) n -> TC n ()
  eqsBnd (B n q ty) = do
    tyTy <- eqsTm ty
    (tyTy ~= Type_) Certain

  eqsTm : Term n -> TC n (Ty n)
  eqsTm (P n) = lookupGlobal n <&> .type
  eqsTm (V i) = lookup i <&> .type
  eqsTm (Lam b rhs) = do
    eqsBnd b
    Pi b <$> withBnd b (eqsTm rhs)
  eqsTm (Pi b rhs) = do
    eqsBnd b
    withBnd b $ do
      rhsTy <- eqsTm rhs
      (rhsTy ~= Type_) Certain
    pure Type_
  eqsTm (App q f x) = do
    fTy <- redTC WHNF =<< eqsTm f
    xTy <- eqsTm x
    case fTy of
      Pi (B piN piQ piTy) piRhs => do
        (piTy ~= xTy) Certain
        pure $ subst (substFZ x) piRhs

      _ => throw . NotPi =<< prettyCtx fTy

  eqsTm Type_ = pure Type_
  eqsTm (Meta (MNValue i)) = pure $ Meta (MNType i)
  eqsTm (Meta (MNType _)) = pure Type_
  eqsTm tm = throw . CantInfer =<< prettyCtx tm

mutual
  eqsPat : Pat (Maybe Q) n -> TC n (Ty n)
  eqsPat (PV i) = lookup i <&> .type
  eqsPat (PCtorApp (Forced cn) args) = do
    cTy <- lookupGlobal cn <&> .type
    eqsPatApp cTy args
  eqsPat (PCtorApp (Checked cn) args) = do
    cTy <- lookupGlobal cn <&> .type
    eqsPatApp cTy args
  eqsPat (PForced tm) = eqsTm tm
  eqsPat PWildcard = throw CantInferWildcard

  eqsPatApp : Term n -> List (Maybe Q, Pat (Maybe Q) n) -> TC n (Ty n)
  eqsPatApp fTy [] = pure fTy
  eqsPatApp fTy ((q,x) :: xs) = do
    xTy <- eqsPat x
    redTC WHNF fTy >>= \case
      Pi (B piN piQ piTy) piRhs => do
        (piTy ~= xTy) Certain
        eqsPatApp (subst (substFZ $ patToTm x) piRhs) xs

      fTyWHNF => throw . NotPi =<< prettyCtx fTyWHNF

eqsCtx : Context (Maybe Q) n -> TC Z ()
eqsCtx [] = pure ()
eqsCtx (b :: bs) = do
  eqsCtx bs
  withCtx bs $ eqsBnd b

eqsClause : Binding (Maybe Q) Z -> Clause (Maybe Q) argn -> TC Z ()
eqsClause fbnd (MkClause pi lhs rhs) = do
  eqsCtx pi
  withCtx pi $ do
    lhsTy <- eqsPatApp (weakenClosed fbnd.type) (toList lhs)
    rhsTy <- eqsTm rhs
    (lhsTy ~= rhsTy) Certain

eqsBody : Binding (Maybe Q) Z -> Body (Maybe Q) -> TC Z ()
eqsBody fbnd Postulate = pure ()
eqsBody fbnd (Constructor arity) = pure ()
eqsBody fbnd (Foreign code) = pure ()
eqsBody fbnd (Clauses argn cs) = traverse_ (eqsClause fbnd) cs

eqsDef : Definition (Maybe Q) -> TC Z ()
eqsDef (MkDef b body) = do
  eqsBnd b
  eqsBody b body

eqsGlobals : TC Z ()
eqsGlobals = do
  gs <- getGlobals
  traverse_ (traverse_ eqsDef) $ toBlocks gs

export
gatherEqualities : Globals (Maybe Q) -> Either (Failure Error) (List Equality)
gatherEqualities gs = run gs [] eqsGlobals <&> .output