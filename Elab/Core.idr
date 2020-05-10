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

record Equality (q : Type) where
  constructor MkE
  {0 n : Nat}
  certainty : Certainty
  context : Context q n
  lhs : TT q n
  rhs : TT q n

TC : Type -> Nat -> Type -> Type
TC q n a = TC Error (List (Equality q)) q n a

cantConvert : ShowQ q => TT q n -> TT q n -> TC q n a
cantConvert lhs rhs = do
  lhsD <- prettyCtx lhs
  rhsD <- prettyCtx rhs
  throw $ CantConvert lhsD rhsD

mutual
  infix 3 ~=
  (~=) : ShowQ q => TT q n -> TT q n -> TC q n ()
  lhs ~= rhs = do
    lhsWHNF <- redTC WHNF lhs
    rhsWHNF <- redTC WHNF rhs
    conv Certain lhsWHNF rhsWHNF

  conv : ShowQ q => Certainty -> TT q n -> TT q n -> TC q n ()
  conv c (V i) (V j) =
    if i == j
      then pure ()
      else cantConvert (V i) (V j)
  conv c (P n) (P n')
    if n == n'
      then pure ()
      else cantConvert (P n) (P n')
  conv c (Lam b@(B n q ty) rhs) (Lam (B n' q' ty') rhs') = do
    ty ~= ty'
    withBnd b $
      rhs ~= rhs'
  conv c (Pi b@(B n q ty) rhs) (Pi (B n' q' ty') rhs') = do
    ty ~= ty'
    withBnd b $
      rhs ~= rhs'
  conv c (App q f x) (App q' f' x') =
    

  conv c Type_ Type_ = pure ()
  conv c (Meta i) tm = do
    ctx <- getCtx
    emit [MkE c ctx (Meta i) tm]
  conv c lhs rhs = cantConvert lhs rhs

mutual
  eqsBnd : ShowQ q => Binding q n -> TC q n ()
  eqsBnd (B n q ty) = do
    tyTy <- eqsTm ty
    tyTy ~= Type_

  eqsTm : ShowQ q => TT q n -> TC q n (TT q n)
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
  eqsPat : ShowQ q => Pat q n -> TC q n (TT q n)
  eqsPat (PV i) = lookup i <&> .type
  eqsPat (PCtorApp (Forced cn) args) = do
    cTy <- lookupGlobal cn <&> .type
    eqsPatApp cTy args
  eqsPat (PCtorApp (Checked cn) args) = do
    cTy <- lookupGlobal cn <&> .type
    eqsPatApp cTy args
  eqsPat (PForced tm) = eqsTm tm
  eqsPat PWildcard = throw CantInferWildcard

  eqsPatApp : ShowQ q => TT q n -> List (q, Pat q n) -> TC q n (TT q n)
  eqsPatApp fTy [] = pure fTy
  eqsPatApp fTy ((q,x) :: xs) = do
    xTy <- eqsPat x
    redTC WHNF fTy >>= \case
      Pi (B piN piQ piTy) piRhs => do
        piTy ~= xTy
        eqsPatApp (subst (substFZ $ patToTm x) piRhs) xs

      fTyWHNF => throw . NotPi =<< prettyCtx fTyWHNF

eqsCtx : ShowQ q => Context q n -> TC q Z ()
eqsCtx [] = pure ()
eqsCtx (b :: bs) = do
  eqsCtx bs
  withCtx bs $ eqsBnd b

eqsClause : ShowQ q => Binding q Z -> Clause q argn -> TC q Z ()
eqsClause fbnd (MkClause pi lhs rhs) = do
  eqsCtx pi
  withCtx pi $ do
    lhsTy <- eqsPatApp (weakenClosed fbnd.type) (toList lhs)
    rhsTy <- eqsTm rhs
    lhsTy ~= rhsTy

eqsBody : ShowQ q => Binding q Z -> Body q -> TC q Z ()
eqsBody fbnd Postulate = pure ()
eqsBody fbnd (Constructor arity) = pure ()
eqsBody fbnd (Foreign code) = pure ()
eqsBody fbnd (Clauses argn cs) = traverse_ (eqsClause fbnd) cs

eqsDef : ShowQ q => Definition q -> TC q Z ()
eqsDef (MkDef b body) = do
  eqsBnd b
  eqsBody b body

eqsGlobals : ShowQ q => TC q Z ()
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
elab : ShowQ q => Globals q -> Either Error (Globals q)
elab gs = ?rhsElab
