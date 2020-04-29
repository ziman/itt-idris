module Core.Check

import public Core.TT
import Core.Normalise
import Core.TT.Pretty
import Utils.Pretty
import Utils.Misc
import Utils.OrdSemiring

import Data.Fin
import Data.List
import Data.Vect
import Data.Strings

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
  QuantityMismatch : (dn : String) -> (dq : Q) -> (inferredQ : Q) -> ErrorMessage n
  AppQuantityMismatch : (fTy : Ty n) -> (tm : Term n) -> ErrorMessage n
  NotPi : Ty n -> ErrorMessage n
  CantCheckErased : ErrorMessage n
  NotImplemented : ErrorMessage n
  WHNFError : EvalError -> ErrorMessage n
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
showEM ctx (WHNFError e)
    = "WHNF error: " ++ show e
showEM ctx CantCheckErased
    = "can't check erased terms"
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
Usage : Nat -> Type
Usage n = Vect n Q

usage0 : Context Q n -> Vect n Q
usage0 [] = []
usage0 (_ :: ctx) = semi0 :: usage0 ctx

usage0e : Env n -> Vect n Q
usage0e env = usage0 env.context

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
getCtx = .context <$> getEnv

getGlobals : TC n (Globals Q)
getGlobals = .globals <$> getEnv

throw : ErrorMessage n -> TC n a
throw msg = MkTC $ \env, st
    => Left (MkF env.backtrace _ env.context msg)

debugThrow : Doc -> TC n a
debugThrow = throw . Debug

withBnd : Binding Q n -> TC (S n) a -> TC n a
withBnd b@(B n q ty) (MkTC f) = MkTC $ \env, st => case env of
  MkE r gs ctx bt => case f (MkE r gs (b :: ctx) bt) st of
    Left fail => Left fail
    Right (st', q' :: us, x) =>
        if q' .<=. q
           then Right (st', us, x)
           else Left (MkF bt _ ctx $ QuantityMismatch n q q')

withTele : Telescope Q n pn -> TC (pn + n) a -> TC n a
withTele [] x = x
withTele (b :: bs) x = withTele bs $ withBnd b x
-- todo: is this the right order?

withBnd0 : Binding Q n -> TC (S n) a -> TC n a
withBnd0 b@(B n q ty) (MkTC f) = MkTC $ \env, st => case env of
  MkE r gs ctx bt => case f (MkE r gs (b :: ctx) bt) st of
    Left fail => Left fail
    Right (st', q' :: us, x) => Right (st', us, x)  -- don't check the quantity

withQ : Q -> TC n a -> TC n a
withQ q (MkTC f) = MkTC $ \env, st => f (record { quantity $= (.*. q) } env) st

useEnv : Q -> Fin n -> Context Q n -> Usage n
useEnv q  FZ    (_ :: ctx) = q :: usage0 ctx
useEnv q (FS x) (_ :: ctx) = semi0 :: useEnv q x ctx

use : Fin n -> TC n ()
use i = MkTC $ \env, st => Right (st, useEnv env.quantity i env.context, ())

lookup : Fin n -> TC n (Ty n)
lookup i = .type . lookup i <$> getCtx

trace : Show tr => tr -> TC n a -> TC n a
trace t (MkTC f) = MkTC $ \env, st => case env of
  MkE r gs ctx bt => f (MkE r gs ctx (show t :: bt)) st

traceTm : Show tr => Term n -> tr -> TC n a -> TC n a
traceTm tm t (MkTC f) = MkTC $ \env, st => case env of
  MkE r gs ctx bt =>
    let msg = show t ++ ": " ++ showTm ctx tm
      in f (MkE r gs ctx (msg :: bt)) st

covering
whnfTC : TT Q n -> TC n (TT Q n)
whnfTC tm = do
  gs <- getGlobals
  case whnf gs tm of
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
    throw NotImplemented
    -- useGlob n

  checkTm tm@(V i) = traceTm tm "VAR" $ use i *> lookup i

  checkTm tm@(Lam b@(B n q ty) rhs) = traceTm tm "LAM" $ do
    tyTy <- withQ I $ checkTm ty
    tyTy ~= Type_

    Pi b <$> (withBnd b $ checkTm rhs)

  checkTm tm@(Pi b@(B n q ty) rhs) = traceTm tm "PI" $ do
    tyTy <- withQ I $ checkTm ty
    tyTy ~= Type_

    withQ I $ withBnd b $ do
      rhsTy <- checkTm rhs
      rhsTy ~= Type_

    pure Type_

  checkTm tm@(App appQ f x) = traceTm tm "APP" $ do
    fTy <- whnfTC =<< checkTm f
    xTy <- checkTm x
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
