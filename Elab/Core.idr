module Elab.Core

import public Core.Globals

import Core.TC
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

data Certainty = Certain | Uncertain

Semigroup Certainty where
  Certain <+> Certain = Certain
  _ <+> _ = Uncertain

record Equality where
  constructor MkE
  {0 n : Nat}
  certainty : Certainty
  context : Context (Maybe Q) n
  lhs : TT (Maybe Q) n
  rhs : TT (Maybe Q) n

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

censorEqs : Maybe Q -> List Equality -> List Equality
censorEqs (Just I) = const []
censorEqs Nothing  = map record{ certainty = Uncertain }
censorEqs _        = id

mutual
  infix 3 ~=
  (~=) : Term n -> Term n -> TC n ()
  lhs ~= rhs = do
    lhsWHNF <- redTC WHNF lhs
    rhsWHNF <- redTC WHNF rhs
    conv lhsWHNF rhsWHNF

  conv : Term n -> Term n -> TC n ()
  conv (V i) (V j) =
    if i == j
      then pure ()
      else cantConvert (V i) (V j)
  conv (P n) (P n') =
    if n == n'
      then pure ()
      else cantConvert (P n) (P n')
  conv (Lam b@(B n q ty) rhs) (Lam (B n' q' ty') rhs') = do
    q ~~ q'
    ty ~= ty'
    withBnd b $
      rhs ~= rhs'
  conv (Pi b@(B n q ty) rhs) (Pi (B n' q' ty') rhs') = do
    q ~~ q'
    ty ~= ty'
    withBnd b $
      rhs ~= rhs'
  conv (App q f x) (App q' f' x') = do
    q ~~ q'
    f ~= f'
    censor (censorEqs q) $
      x ~= x'
  conv Type_ Type_ = pure ()
  conv (Meta i) tm = do
    ctx <- getCtx
    emit [MkE Certain ctx (Meta i) tm]
  conv tm (Meta i) = do
    ctx <- getCtx
    emit [MkE Certain ctx (Meta i) tm]
  conv lhs rhs = cantConvert lhs rhs

mutual
  eqsBnd : Binding (Maybe Q) n -> TC n ()
  eqsBnd (B n q ty) = do
    tyTy <- eqsTm ty
    tyTy ~= Type_

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
      rhsTy ~= Type_
    pure Type_
  eqsTm (App q f x) = do
    fTy <- redTC WHNF =<< eqsTm f
    xTy <- eqsTm x
    case fTy of
      Pi (B piN piQ piTy) piRhs => do
        piTy ~= xTy
        pure $ subst (substFZ x) piRhs

      _ => throw . NotPi =<< prettyCtx fTy

  eqsTm Type_ = pure Type_
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
        piTy ~= xTy
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
    lhsTy ~= rhsTy

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

numberMetas : Globals (Maybe Q) -> Globals (Maybe Q)
numberMetas gs = evalState (mlGlobals numberMeta gs) 0
  where
    numberMeta : Int -> State Int (Either Int (n ** Term n))
    numberMeta _ = do
      i <- get
      put (i+1)
      pure $ Left i

export
elab : Globals (Maybe Q) -> Either Error (Globals (Maybe Q))
elab gs = ?rhsElab
