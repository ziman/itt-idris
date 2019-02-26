module Check

import TT
import Data.Fin

%default total
%hide Language.Reflection.V

record TCState where
  constructor MkTS

Backtrace : Type
Backtrace = List String

data ErrorMessage : Type where
  OtherError : String -> ErrorMessage
  CantConvert : TT Q n -> TT Q n -> ErrorMessage
  RunawayReduction : TT Q n -> ErrorMessage

record Failure where
  constructor MkF
  backtrace : Backtrace
  errorMessage : ErrorMessage

record Env (n : Nat) where
  constructor MkE
  context : Context Q n
  backtrace : Backtrace

record TC (n : Nat) (a : Type) where
  constructor MkTC
  runTC : Env n -> TCState -> Either Failure (TCState, a)

Functor (TC n) where
  map f (MkTC g) = MkTC $ \env, st => case g env st of
    Left fail => Left fail
    Right (st', x) => Right (st', f x)

Applicative (TC n) where
  pure x = MkTC $ \env, st => Right (st, x)
  (<*>) (MkTC f) (MkTC g) = MkTC $ \env, st =>
    case f env st of
        Left fail => Left fail
        Right (st', f') => case g env st' of
            Left fail => Left fail
            Right (st'', x') => Right (st'', f' x')

Monad (TC n) where
  (>>=) (MkTC f) g = MkTC $ \env, st =>
    case f env st of
        Left fail => Left fail
        Right (st', x) => case g x of
            MkTC h => h env st'

getEnv : TC n (Env n)
getEnv = MkTC $ \env, st => Right (st, env)

getCtx : TC n (Context Q n)
getCtx = context <$> getEnv

throw : ErrorMessage -> TC n a
throw msg = MkTC $ \env, st
    => Left (MkF (backtrace env) msg)

Term : Nat -> Type
Term = TT Q

Ty : Nat -> Type
Ty = TT Q

withDef : Def Q n -> TC (S n) a -> TC n a
withDef d (MkTC f) = MkTC $ \env, st => case env of
  MkE ctx bt => f (MkE (ctx |> d) bt) st

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

checkTm : Term n -> TC n (Ty n)
checkTm (V i) = ?rhs_1
checkTm (Bind b d rhs) = ?rhs_2
checkTm (App x f y) = ?rhs_3
checkTm Star = ?rhs_4