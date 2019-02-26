module Check

import TT
import OrdSemiring

import Data.Fin
import Data.Vect

%default total
%hide Language.Reflection.V

record TCState where
  constructor MkTS

Backtrace : Type
Backtrace = List String

Term : Nat -> Type
Term = TT Q

Ty : Nat -> Type
Ty = TT Q

data ErrorMessage : Type where
  OtherError : String -> ErrorMessage
  CantConvert : TT Q n -> TT Q n -> ErrorMessage
  RunawayReduction : Term n -> ErrorMessage
  QuantityMismatch : (n : String) -> (dq : Q) -> (inferredQ : Q) -> ErrorMessage
  AppQuantityMismatch : (fTy : Ty n) -> (tm : Term n) -> ErrorMessage
  NotPi : Ty n -> ErrorMessage

record Failure where
  constructor MkF
  backtrace : Backtrace
  errorMessage : ErrorMessage

record Env (n : Nat) where
  constructor MkE
  quantity : Q
  context : Context Q n
  backtrace : Backtrace

Usage : Nat -> Type
Usage n = Vect n Q

usage0 : Context Q n -> Vect n Q
usage0 [] = []
usage0 (ctx |> _) = semi0 :: usage0 ctx

usage0e : Env n -> Vect n Q
usage0e (MkE r ctx bt) = usage0 ctx

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

throw : ErrorMessage -> TC n a
throw msg = MkTC $ \env, st
    => Left (MkF (backtrace env) msg)

withDef : Def Q n -> TC (S n) a -> TC n a
withDef d@(D n q ty) (MkTC f) = MkTC $ \env, st => case env of
  MkE r ctx bt => case f (MkE r (ctx |> d) bt) st of
    Left fail => Left fail
    Right (st', q' :: us, x) =>
        if q' .<=. q
           then Right (st', us, x)
           else Left (MkF bt $ QuantityMismatch n q q')

withDef0 : Def Q n -> TC (S n) a -> TC n a
withDef0 d@(D n q ty) (MkTC f) = MkTC $ \env, st => case env of
  MkE r ctx bt => case f (MkE r (ctx |> d) bt) st of
    Left fail => Left fail
    Right (st', _q' :: us, x) => Right (st', us, x)  -- don't check the quantity

withQ : Q -> TC n a -> TC n a
withQ q (MkTC f) = MkTC $ \env, st => f (record { quantity $= (.*. q) } env) st

useEnv : Q -> Fin n -> Context Q n -> Usage n
useEnv q  FZ    (ctx |> _) = q :: usage0 ctx
useEnv q (FS x) (ctx |> _) = semi0 :: useEnv q x ctx

use : Fin n -> TC n ()
use i = MkTC $ \env, st => Right (st, useEnv (quantity env) i (context env), ())

lookup : Fin n -> TC n (Ty n)
lookup i = defType . lookupCtx i <$> getCtx

rnfTC : TT Q n -> TC n (TT Q n)
rnfTC = nf 8
  where
    nf : Nat -> TT Q n -> TC n (TT Q n)
    nf  Z tm = throw $ RunawayReduction tm

    nf (S fuel) (V i) = pure (V i)

    nf (S fuel) (Bind b (D n q ty) rhs) = do
      ty' <- nf fuel ty
      let d' = D n q ty'
      Bind b d' <$> withDef d' (nf fuel rhs)

    nf (S fuel) (App q f x) = do
      f' <- nf fuel f
      x' <- nf fuel x
      case f' of
        Bind Lam _d rhs => nf fuel $ substVars (substTop x') rhs
        _ => pure $ App q f' x'

    nf (S fuel) Star = pure Star

conv : TT Q n -> TT Q n -> TC n ()
conv p q = throw $ CantConvert p q

infix 3 ~=
covering
(~=) : TT Q n -> TT Q n -> TC n ()
(~=) p q = do
  p' <- rnfTC p
  q' <- rnfTC q
  conv p' q'

infixl 2 =<<
(=<<) : Monad m => (a -> m b) -> m a -> m b
(=<<) f x = x >>= f

checkTm : Term n -> TC n (Ty n)
checkTm (V i) = use i *> lookup i
checkTm (Bind Lam d@(D n q ty) rhs) = do
  tyTy <- checkTm ty
  tyTy ~= Star

  Bind Pi d <$> (withDef d $ checkTm rhs)

checkTm (Bind Pi d@(D n q ty) rhs) = do
  tyTy <- checkTm ty
  tyTy ~= Star

  withDef0 d $ do
    rhsTy <- checkTm rhs
    rhsTy ~= Star

  pure Star

checkTm tm@(App appQ f x) = do
  fTy <- rnfTC =<< checkTm f
  xTy <- checkTm x
  case fTy of
    Bind Pi (D piN piQ piTy) piRhs =>
        if piQ /= appQ
           then throw $ AppQuantityMismatch fTy tm
           else do
             xTy ~= piTy
             pure $ substVars (substTop x) piRhs

    _ => throw $ NotPi fTy

checkTm Star = pure Star
