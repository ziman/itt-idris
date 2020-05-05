module Core.Check

import public Core.TT
import Core.Normalise
import Core.TT.Pretty
import Utils.Pretty
import Utils.Misc
import Core.Quantity
import Utils.OrdSemiring

import Data.Fin
import Data.List
import Data.Vect
import Data.Strings
import public Data.SortedMap

%default total
%undotted_record_projections off

public export
record TCState where
  constructor MkTCS

public export
Term : Nat -> Type
Term = TT Q

public export
Ty : Nat -> Type
Ty = TT Q

public export
data ErrorMessage : Nat -> Type where
  CantConvert : TT Q n -> TT Q n -> ErrorMessage n
  NotLeq : (p, q : Q) -> ErrorMessage n
  QuantityMismatch : (dn : String) -> (dq : Q) -> (inferredQ : Q) -> ErrorMessage n
  AppQuantityMismatch : (fTy : Ty n) -> (tm : Term n) -> ErrorMessage n
  NotPi : Ty n -> ErrorMessage n
  CantCheckErased : ErrorMessage n
  CantCheckWildcard : ErrorMessage n
  NotImplemented : ErrorMessage n
  WHNFError : EvalError -> ErrorMessage n
  UnknownGlobal : Name -> ErrorMessage n
  Debug : Doc -> ErrorMessage n

showEM : Context Q n -> ErrorMessage n -> String
showEM ctx (CantConvert x y)
    = "can't convert: " ++ showTm ctx x ++ " with " ++ showTm ctx y
showEM ctx (QuantityMismatch dn dq inferredQ)
    = "quantity mismatch in " ++ show dn ++ ": annotated " ++ show dq ++ ", inferred " ++ show inferredQ
showEM ctx (AppQuantityMismatch fTy tm)
    = "quantity mismatch in application of (_ : " ++ showTm ctx fTy ++ "): " ++ showTm ctx tm
showEM ctx (NotLeq p q)
    = "rules require that " ++ show p ++ " ≤ " ++ show q
showEM ctx (NotPi x)
    = "not a pi: " ++ showTm ctx x
showEM ctx (WHNFError e)
    = "normalisation error: " ++ show e
showEM ctx (UnknownGlobal n)
    = "unknown global: " ++ show n
showEM ctx CantCheckErased
    = "can't check erased terms"
showEM ctx CantCheckWildcard
    = "can't check wildcard patterns"
showEM ctx NotImplemented
    = "not implemented yet"
showEM ctx (Debug doc)
    = render "  " (text ">>> DEBUG <<< " $$ indent doc)

public export
Backtrace : Type
Backtrace = List String

public export
record Failure where
  constructor MkF
  backtrace : Backtrace
  0 n : Nat
  context : Context Q n
  errorMessage : ErrorMessage n

export
Show Failure where
  show (MkF bt _ ctx msg) = "With backtrace:\n"
    ++ unlines (reverse $ map ("  " ++) bt)
    ++ showEM ctx msg

public export
record Env (n : Nat) where
  constructor MkE
  quantity : Q
  globals : Globals Q
  context : Context Q n
  backtrace : Backtrace

public export
record Usage (n : Nat) where
  constructor MkUsage
  global : SortedMap Name Q
  local : Vect n Q

localUsage0 : Context Q n -> Vect n Q
localUsage0 [] = []
localUsage0 (_ :: ctx) = semi0 :: localUsage0 ctx

localUsage0e : Env n -> Vect n Q
localUsage0e env = localUsage0 env.context

Semigroup (Usage n) where
  MkUsage g l <+> MkUsage g' l'
    = MkUsage (mergeWith (.+.) g g') (zipWith (.+.) l l')

usage0 : Context Q n -> Usage n
usage0 ctx = MkUsage empty (localUsage0 ctx)

public export
record TC (n : Nat) (a : Type) where
  constructor MkTC
  run : Env n -> TCState -> Either Failure (TCState, Usage n, a)

Functor (TC n) where
  map f (MkTC g) = MkTC $ \env, st => case g env st of
    Left fail => Left fail
    Right (st', us, x) => Right (st', us, f x)

Applicative (TC n) where
  pure x = MkTC $ \env, st => Right (st, usage0 env.context, x)
  (<*>) (MkTC f) (MkTC g) = MkTC $ \env, st =>
    case f env st of
        Left fail => Left fail
        Right (st', us', f') => case g env st' of
            Left fail => Left fail
            Right (st'', us'', x'') => Right (st'', us' <+> us'', f' x'')

Monad (TC n) where
  (>>=) (MkTC f) g = MkTC $ \env, st =>
    case f env st of
        Left fail => Left fail
        Right (st', us, x) => case g x of
            MkTC h => case h env st' of
                Left fail => Left fail
                Right (st'', us'', x'') => Right (st'', us <+> us'', x'')

getEnv : TC n (Env n)
getEnv = MkTC $ \env, st => Right (st, usage0 env.context, env)

getCtx : TC n (Context Q n)
getCtx = .context <$> getEnv

getGlobals : TC n (Globals Q)
getGlobals = .globals <$> getEnv

withMutualBlock : List (Definition Q) -> TC n a -> TC n a
withMutualBlock ds (MkTC f) = MkTC $ \env, st =>
  f (record {globals $= \g => g `snocBlock` ds} env) st

throw : ErrorMessage n -> TC n a
throw msg = MkTC $ \env, st
    => Left (MkF env.backtrace _ env.context msg)

debugThrow : Doc -> TC n a
debugThrow = throw . Debug

withBnd : Binding Q n -> TC (S n) a -> TC n a
withBnd b@(B n q ty) (MkTC f) = MkTC $ \env, st => case env of
  MkE r gs ctx bt => case f (MkE r gs (b :: ctx) bt) st of
    Left fail => Left fail
    Right (st', MkUsage ug (q' :: us), x) =>
        if isBinderUsageOk q q'
           then Right (st', MkUsage ug us, x)
           else Left (MkF bt _ ctx $ QuantityMismatch n q q')

withCtx : Context Q n -> TC n a -> TC Z a
withCtx [] tc = tc
withCtx (b :: bs) tc = withCtx bs $ withBnd b tc

withQ : Q -> TC n a -> TC n a
withQ q (MkTC f) = MkTC $ \env, st => f (record { quantity $= (.*. q) } env) st

useEnv : Q -> Fin n -> Context Q n -> Vect n Q
useEnv q  FZ    (_ :: ctx) = q :: localUsage0 ctx
useEnv q (FS x) (_ :: ctx) = semi0 :: useEnv q x ctx

use : Fin n -> TC n ()
use i = MkTC $ \env, st => Right (st, MkUsage empty (useEnv env.quantity i env.context), ())

useGlobal : Name -> TC n ()
useGlobal n = MkTC $ \env, st =>
  Right (st, MkUsage (insert n semi1 empty) (localUsage0 env.context), ())

(<=) : Q -> Q -> TC n ()
p <= q =
  if p <= q
    then pure ()
    else throw $ NotLeq p q

lookup : Fin n -> TC n (Binding Q n)
lookup i = lookup i <$> getCtx

lookupGlobal : Name -> TC n (Binding Q n)
lookupGlobal n =
  (lookup n <$> getGlobals) >>= \case
    Nothing => throw $ UnknownGlobal n
    Just d  => pure $ weakenClosedBinding d.binding

trace : Show tr => tr -> TC n a -> TC n a
trace t (MkTC f) = MkTC $ \env, st => case env of
  MkE r gs ctx bt => f (MkE r gs ctx (show t :: bt)) st

traceTm : Show tr => Term n -> tr -> TC n a -> TC n a
traceTm tm t (MkTC f) = MkTC $ \env, st => case env of
  MkE r gs ctx bt =>
    let msg = show t ++ ": " ++ showTm ctx tm
      in f (MkE r gs ctx (msg :: bt)) st

traceCtx : (Show tr, Pretty (Context Q n) b) => b -> tr -> TC n a -> TC n a
traceCtx bv t (MkTC f) = MkTC $ \(MkE r gs ctx bt), st
  => let msg = show t ++ ": " ++ (render "  " $ pretty ctx bv)
      in f (MkE r gs ctx (msg :: bt)) st

traceDoc : Show tr => Doc -> tr -> TC n a -> TC n a
traceDoc doc t (MkTC f) = MkTC $ \(MkE r gs ctx bt), st
  => let msg = render "  " (text (show t) <+> text ": " <++> doc)
      in f (MkE r gs ctx (msg :: bt)) st

covering
whnfTC : TT Q n -> TC n (TT Q n)
whnfTC tm = do
  gs <- getGlobals
  case red WHNF gs tm of
    Left e => throw $ WHNFError e
    Right tm' => pure tm'

infix 3 ~=
mutual
  covering
  conv : TT Q n -> TT Q n -> TC n ()

  conv (P n) (P n') =
    if n == n'
      then pure ()
      else throw $ CantConvert (P n) (P n')

  conv (V i) (V j) =
    if finEq i j
      then pure ()
      else throw $ CantConvert (V i) (V j)

  conv ltm@(Lam b@(B n q ty) rhs) rtm@(Lam b'@(B n' q' ty') rhs') =
    if q /= q'
      then throw $ CantConvert ltm rtm
      else do
        ty ~= ty'
        withBnd b $ rhs ~= rhs'

  conv ltm@(Pi b@(B n q ty) rhs) rtm@(Pi b'@(B n' q' ty') rhs') =
    if q /= q'
      then throw $ CantConvert ltm rtm
      else do
        ty ~= ty'
        withBnd b $ rhs ~= rhs'

  conv lhs@(App q f x) rhs@(App q' f' x') =
    if q /= q'
      then throw $ CantConvert lhs rhs
      else do
        f ~= f'
        case q of
          I => pure ()
          _ => x ~= x'

  conv Type_ Type_ = pure ()

  conv p q = throw $ CantConvert p q

  covering
  (~=) : TT Q n -> TT Q n -> TC n ()
  (~=) p q = do
    p' <- whnfTC p
    q' <- whnfTC q
    conv p' q'

mutual
  covering export
  checkTm : Term n -> TC n (Ty n)
  checkTm tm@(P n) = traceTm tm "GLOB" $ do
    b <- lookupGlobal n
    useGlobal (UN b.name)
    pure $ b.type

  checkTm tm@(V i) = traceTm tm "VAR" $ do
    b <- lookup i
    use i
    pure b.type

  checkTm tm@(Lam b@(B n q ty) rhs) = traceTm tm "LAM" $ do
    tyTy <- withQ I $ checkTm ty
    tyTy ~= Type_

    Pi b <$> (withBnd b $ checkTm rhs)

  checkTm tm@(Pi b@(B n q ty) rhs) = traceTm tm "PI" $ do
    tyTy <- withQ I $ checkTm ty
    tyTy ~= Type_

    withQ I $ withBnd (B n I ty) $ do
      rhsTy <- checkTm rhs
      rhsTy ~= Type_

    pure Type_

  checkTm tm@(App appQ f x) = traceTm tm "APP" $ do
    fTy <- whnfTC =<< checkTm f
    xTy <- withQ appQ $ checkTm x
    case fTy of
      Pi (B piN piQ piTy) piRhs =>
          if piQ /= appQ
             then throw $ AppQuantityMismatch fTy tm
             else do
               xTy ~= piTy
               pure $ subst (substFZ x) piRhs

      _ => throw $ NotPi fTy

  checkTm Type_ = pure Type_
  checkTm Erased = throw CantCheckErased

mutual
  -- (how many times we inspect, type)
  covering export
  checkPat : Q -> Pat Q n -> TC n (Q, Ty n)
  checkPat fq pat@(PV i) = traceCtx pat "PV" $ do
    b <- lookup i
    pure (b.qv, b.type)

  checkPat fq pat@(PCtorApp ctor args) = traceCtx pat "PAPP" $ do
    -- TODO: check that cn is really a constructor, not a pattern matching function/postulate or such
    (cq, cTy) <- case the PCtor ctor of
      Forced cn => do
        b <- lookupGlobal cn
        pure (I, b.type)
      Checked cn => do
        b <- lookupGlobal cn

        -- we don't construct the value so we don't place requirements on the quantity of the constructor
        -- if the function is bound at least L
        -- then we want to have the constructor bound at least L (but never require more)
        -- (L .*. fq) <= b.qv

        -- L because we inspect the constructor tag exactly once
        pure (L, b.type)

    (argsQ, argsTy) <- checkPatApp fq cTy args
    pure (cq .\/. argsQ, argsTy)

  checkPat fq pat@(PForced tm) = traceCtx pat "PFORCED" $ do
    tmTy <- withQ I $ checkTm tm
    pure (I, tmTy)  -- no usage here

  checkPat fq PWildcard =
    throw CantCheckWildcard

  covering export
  checkPatApp : Q -> TT Q n -> List (Q, Pat Q n) -> TC n (Q, Ty n)
  checkPatApp fq fTy [] = pure (I, fTy)  -- no usage here
  checkPatApp fq fTy ((appQ, pat) :: pats) = do
    (patQ, patTy) <- checkPat fq pat
    patQ <= appQ  -- we have enough term to feed this pattern

    whnfTC fTy >>= \case
      Pi b@(B piN piQ piTy) piRhs => do
        patTy ~= piTy
        appQ <= piQ
        piQ <= appQ
        (patsQ, patsTy) <-
          checkPatApp fq
            (subst (substFZ $ patToTm pat) piRhs)
            pats

        pure (patQ .\/. patsQ, patsTy)

      _ => throw $ NotPi fTy

covering
checkBinding : Binding Q n -> TC n ()
checkBinding (B n q ty) = do
  tyTy <- withQ I $ checkTm ty
  tyTy ~= Type_

covering
checkCtx : Context Q n -> TC Z ()
checkCtx [] = pure ()
checkCtx (b :: bs) = do
  checkCtx bs
  withCtx bs $ traceCtx b "BINDING" $ do
    checkBinding b

covering
checkClause : {argn : Nat} -> Binding Q Z -> Clause Q argn -> TC Z ()
checkClause fbnd c@(MkClause pi lhs rhs) = traceDoc (pretty (UN fbnd.name) c) "CLAUSE" $ do
  checkCtx pi
  withCtx pi $ do
    -- we ignore lhsQ because we have enough function (cf. supplying R in Infer.inferClause)
    (_, lhsTy) <- checkPatApp fbnd.qv (weakenClosed fbnd.type) (toList lhs)
    rhsTy <- checkTm rhs  -- we always need to construct one of RHS per call
    traceTm lhsTy "CLAUSE-CONV" $ do
      lhsTy ~= rhsTy

covering
checkBody : Binding Q Z -> Body Q -> TC Z ()
checkBody bnd Postulate = pure ()
checkBody bnd Constructor = pure ()
checkBody bnd (Foreign code) = pure ()
checkBody bnd (Clauses argn cs) = traverse_ (checkClause bnd) cs

covering
checkDefinition : Definition Q -> TC Z ()
checkDefinition d@(MkDef bnd body) = traceDoc (pretty () d) "DEF" $ do
  checkBinding bnd
  checkBody bnd body

covering export
checkDefinitions : List (List (Definition Q)) -> TC Z ()
checkDefinitions [] = pure ()
checkDefinitions (ds :: dss) =
  withMutualBlock ds $
    traverse_ checkDefinition ds

covering export
checkGlobals : TC Z ()
checkGlobals = checkDefinitions . Globals.toBlocks =<< getGlobals
