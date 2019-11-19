module Check

import public ITT.Core
import public ITT.Module
import ITT.Clause
import ITT.Normalise
import ITT.Core.Pretty
import Utils.Pretty
import Utils.Misc
import Utils.OrdSemiring

import Data.Fin
import Data.Vect
import Data.SortedMap as Map

%default total
%hide Language.Reflection.V

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
  QuantityMismatch : (dn : String) -> (dq : Q) -> (inferredQ : Q) -> ErrorMessage n
  AppQuantityMismatch : (fTy : Ty n) -> (tm : Term n) -> ErrorMessage n
  NotPi : Ty n -> ErrorMessage n
  CantCheckErased : ErrorMessage n
  NotImplemented : ErrorMessage n
  UnknownGlobal : Name -> ErrorMessage n
  Debug : Doc -> ErrorMessage n

showEM : Context Q n -> ErrorMessage n -> String
showEM ctx (CantConvert x y)
    = "can't convert: " ++ showTm ctx x ++ " with " ++ showTm ctx y
showEM ctx (QuantityMismatch dn dq inferredQ)
    = "quantity mismatch in " ++ show dn ++ ": declared " ++ show dq ++ " /= inferred " ++ show inferredQ
showEM ctx (AppQuantityMismatch fTy tm)
    = "quantity mismatch in application of (_ : " ++ showTm ctx fTy ++ "): " ++ showTm ctx tm
showEM ctx (NotPi x)
    = "not a pi: " ++ showTm ctx x
showEM ctx CantCheckErased
    = "can't check erased terms"
showEM ctx NotImplemented
    = "not implemented yet"
showEM ctx (UnknownGlobal n)
    = "unknown global " ++ show n
showEM ctx (Debug doc)
    = render "  " (text ">>> DEBUG <<< " $$ indent doc)

public export
Backtrace : Type
Backtrace = List String

public export
record Failure where
  constructor MkF
  backtrace : Backtrace
  n : Nat
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
  context : Context Q n
  backtrace : Backtrace
  globals : Globals Q

public export
Usage : Nat -> Type
Usage n = Vect n Q

usage0 : Context Q n -> Vect n Q
usage0 [] = []
usage0 (_ :: ctx) = semi0 :: usage0 ctx

usage0e : Env n -> Vect n Q
usage0e (MkE r ctx bt glob) = usage0 ctx

public export
record TC (n : Nat) (a : Type) where
  constructor MkTC
  runTC : Env n -> TCState -> Either Failure (TCState, Usage n, a)

Functor (TC n) where
  map f (MkTC g) = MkTC $ \env, st => case g env st of
    Left fail => Left fail
    Right (st', us, x) => Right (st', us, f x)

Applicative (TC n) where
  pure x = MkTC $ \env, st => Right (st, usage0e env, x)
  (<*>) (MkTC f) (MkTC g) = MkTC $ \env, st =>
    case f env st of
        Left fail => Left fail
        Right (st', us', f') => case g env st' of
            Left fail => Left fail
            Right (st'', us'', x'') => Right (st'', us' <.+.> us'', f' x'')

Monad (TC n) where
  (>>=) (MkTC f) g = MkTC $ \env, st =>
    case f env st of
        Left fail => Left fail
        Right (st', us, x) => case g x of
            MkTC h => case h env st' of
                Left fail => Left fail
                Right (st'', us'', x'') => Right (st'', us <.+.> us'', x'')

getEnv : TC n (Env n)
getEnv = MkTC $ \env, st => Right (st, usage0e env, env)

getCtx : TC n (Context Q n)
getCtx = context <$> getEnv

getGlobals : TC n (Globals Q)
getGlobals = globals <$> getEnv

throw : ErrorMessage n -> TC n a
throw msg = MkTC $ \env, st
    => Left (MkF (backtrace env) _ (context env) msg)

debugThrow : Doc -> TC n a
debugThrow = throw . Debug

withBnd : Binding Q n -> TC (S n) a -> TC n a
withBnd b@(B n q ty) (MkTC f) = MkTC $ \env, st => case env of
  MkE r ctx bt glob => case f (MkE r (b :: ctx) bt glob) st of
    Left fail => Left fail
    Right (st', q' :: us, x) =>
        if q' .<=. q
           then Right (st', us, x)
           else Left (MkF bt _ ctx $ QuantityMismatch n q q')

withTele : Telescope Q n pn -> TC (pn + n) a -> TC n a
withTele [] x = x
withTele (b :: ds) x = withBnd b $ withTele ds x

withBnd0 : Binding Q n -> TC (S n) a -> TC n a
withBnd0 b@(B n q ty) (MkTC f) = MkTC $ \env, st => case env of
  MkE r ctx bt glob => case f (MkE r (b :: ctx) bt glob) st of
    Left fail => Left fail
    Right (st', _q' :: us, x) => Right (st', us, x)  -- don't check the quantity

withGlob : Def Q -> TC n a -> TC n a
withGlob d (MkTC f) = MkTC $ \(MkE r ctx bt glob), st =>
  f (MkE r ctx bt (Map.insert (dn d) d glob)) st

withQ : Q -> TC n a -> TC n a
withQ q (MkTC f) = MkTC $ \env, st => f (record { quantity $= (.*. q) } env) st

useEnv : Q -> Fin n -> Context Q n -> Usage n
useEnv q  FZ    (_ :: ctx) = q :: usage0 ctx
useEnv q (FS x) (_ :: ctx) = semi0 :: useEnv q x ctx

use : Fin n -> TC n ()
use i = MkTC $ \env, st => Right (st, useEnv (quantity env) i (context env), ())

lookup : Fin n -> TC n (Ty n)
lookup i = bty . lookup i <$> getCtx

trace : Show tr => tr -> TC n a -> TC n a
trace t (MkTC f) = MkTC $ \env, st => case env of
  MkE r ctx bt glob => f (MkE r ctx (show t :: bt) glob) st

traceTm : Show tr => Term n -> tr -> TC n a -> TC n a
traceTm tm t (MkTC f) = MkTC $ \env, st => case env of
  MkE r ctx bt glob =>
    let msg = show t ++ ": " ++ showTm ctx tm
      in f (MkE r ctx (msg :: bt) glob) st

infix 3 ~=
mutual
  covering
  conv : TT Q n -> TT Q n -> TC n ()

  conv (V i) (V j) =
    if finEq i j
        then pure ()
        else throw $ CantConvert (V i) (V j)

  conv (G n) (G n') =
    if n == n'
      then pure ()
      else throw $ CantConvert (G n) (G n')

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

  conv ltm@(Let b@(B n q ty) val rhs) rtm@(Let b'@(B n' q' ty') val' rhs') =
    if q /= q'
       then throw $ CantConvert ltm rtm
       else do
         ty ~= ty'
         withBnd b $ do
           val ~= val'
           rhs ~= rhs'

  conv lhs@(App q f x) rhs@(App q' f' x') =
    if q /= q'
       then throw $ CantConvert lhs rhs
       else do
         f ~= f'
         case q of
            I => pure ()
            _ => x ~= x'

  conv Star Star = pure ()

  conv p q = throw $ CantConvert p q

  covering
  (~=) : TT Q n -> TT Q n -> TC n ()
  (~=) p q = do
    glob <- getGlobals
    conv (whnf glob p) (whnf glob q)

infixl 2 =<<
(=<<) : Monad m => (a -> m b) -> m a -> m b
(=<<) f x = x >>= f

mutual
  covering export
  checkTm : Term n -> TC n (Ty n)
  checkTm tm@(V i) = traceTm tm "VAR" $ use i *> lookup i
  checkTm tm@(G n) = traceTm tm "GLOB" $ do
    glob <- getGlobals
    case Module.lookup n glob of
      Nothing => throw $ UnknownGlobal n
      Just (D n q ty b) => pure $ weakenClosed ty

  checkTm tm@(Lam b@(B n q ty) rhs) = traceTm tm "LAM" $ do
    tyTy <- withQ I $ checkTm ty
    tyTy ~= Star

    Pi b <$> (withBnd b $ checkTm rhs)

  checkTm tm@(Pi b@(B n q ty) rhs) = traceTm tm "PI" $ do
    tyTy <- withQ I $ checkTm ty
    tyTy ~= Star

    withQ I $ withBnd b $ do
      rhsTy <- checkTm rhs
      rhsTy ~= Star

    pure Star

  checkTm tm@(Let b@(B n q ty) val rhs) = traceTm tm "LET" $ do
    throw NotImplemented

  checkTm tm@(App appQ f x) = traceTm tm "APP" $ do
    glob <- getGlobals
    fTy <- whnf glob <$> checkTm f
    xTy <- checkTm x
    case fTy of
      Pi (B piN piQ piTy) piRhs =>
          if piQ /= appQ
             then throw $ AppQuantityMismatch fTy tm
             else do
               xTy ~= piTy
               pure $ subst (substFZ x) piRhs

      _ => throw $ NotPi fTy

  checkTm {n} tm@(Match pvs ss rty ct) = traceTm tm "MATCH" $ do
      traverse_ checkClause $ foldMatch pvs ss rty ct
      pure $ substTop pvs ss rty

  checkTm Star = pure Star
  checkTm Erased = throw CantCheckErased

  covering
  checkClause : Clause q n -> TC n ()
  checkClause (C pn pvs ty lhs rhs) = do
    withTele pvs $ do
      rhsTy <- checkTm rhs
      ty ~= rhsTy
    -- todo: check case tree?
    -- todo: check LHS:
    --   1. construct type of F as \Pi (x : \sigma) \to \rho
    --      -> no substitution necessary, this is easy
    --   2. check pattern the standard way
    --   3. get the type of the pattern/LHS
    -- so the tree folding code does not need to subst in rty

  covering
  checkPat : Pat q n pn -> TC n (Ty (pn + n))
  checkPat pat = ?checkPat_rhs

covering export
checkDef : Def Q -> TC Z ()
checkDef (D n q ty body) = trace ("DEF", n) $ do
    tyTy <- checkTm ty
    tyTy ~= Star

    case body of
        Abstract => pure ()
        Constructor => pure ()
        Term tm => withGlob (D n q ty Abstract) $ do
          tmTy <- checkTm tm
          tmTy ~= ty

covering export
checkDefs : List (Def Q) -> TC Z ()
checkDefs [] = pure ()
checkDefs (d :: ds) = do
  checkDef d
  withGlob d $ checkDefs ds
