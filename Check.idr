module Check

import TT
import OrdSemiring

import Data.Fin
import Data.Vect

%default total
%hide Language.Reflection.V

record TCState where
  constructor MkTCS

Backtrace : Type
Backtrace = List String

Term : Nat -> Type
Term = TT Q

Ty : Nat -> Type
Ty = TT Q

data ErrorMessage : Nat -> Type where
  CantConvert : TT Q n -> TT Q n -> ErrorMessage n
  OutOfFuel : Term n -> ErrorMessage n
  QuantityMismatch : (dn : String) -> (dq : Q) -> (inferredQ : Q) -> ErrorMessage n
  AppQuantityMismatch : (fTy : Ty n) -> (tm : Term n) -> ErrorMessage n
  NotPi : Ty n -> ErrorMessage n

showEM : Context Q n -> ErrorMessage n -> String
showEM ctx (CantConvert x y) = "can't convert: " ++ showTm ctx x ++ " with " ++ showTm ctx y
showEM ctx (OutOfFuel x) = "out of fuel: " ++ showTm ctx x
showEM ctx (QuantityMismatch dn dq inferredQ) = "quantity mismatch in " ++ show dn ++ ": declared " ++ show dq ++ " /= inferred " ++ show inferredQ
showEM ctx (AppQuantityMismatch fTy tm) = "quantity mismatch in application (f : " ++ showTm ctx fTy ++ "): " ++ showTm ctx tm
showEM ctx (NotPi x) = "not a pi: " ++ showTm ctx x

record Failure where
  constructor MkF
  backtrace : Backtrace
  n : Nat
  context : Context Q n
  errorMessage : ErrorMessage n

Show Failure where
  show (MkF bt _ ctx msg) = "With backtrace:\n" ++ unlines (map ("  " ++) bt) ++ showEM ctx msg

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

throw : ErrorMessage n -> TC n a
throw msg = MkTC $ \env, st
    => Left (MkF (backtrace env) _ (context env) msg)

withDef : Def Q n -> TC (S n) a -> TC n a
withDef d@(D n q ty) (MkTC f) = MkTC $ \env, st => case env of
  MkE r ctx bt => case f (MkE r (ctx |> d) bt) st of
    Left fail => Left fail
    Right (st', q' :: us, x) =>
        if q' .<=. q
           then Right (st', us, x)
           else Left (MkF bt _ ctx $ QuantityMismatch n q q')

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

trace : Show tr => tr -> TC n a -> TC n a
trace t (MkTC f) = MkTC $ \env, st => case env of
  MkE r ctx bt => f (MkE r ctx (show t :: bt)) st

traceTm : Show tr => Term n -> tr -> TC n a -> TC n a
traceTm tm t (MkTC f) = MkTC $ \env, st => case env of
  MkE r ctx bt =>
    let msg = show t ++ ": " ++ showTm ctx tm
      in f (MkE r ctx (msg :: bt)) st

finEq : Fin n -> Fin n -> Bool
finEq FZ FZ = True
finEq FZ (FS _) = False
finEq (FS _) FZ = False
finEq (FS x) (FS y) = finEq x y

infix 3 ~=
mutual
  covering
  conv : TT Q n -> TT Q n -> TC n ()

  conv (V i) (V j) =
    if finEq i j
        then pure ()
        else throw $ CantConvert (V i) (V j)

  conv ltm@(Bind b d@(D n q ty) rhs) rtm@(Bind b' d'@(D n' q' ty') rhs') =
    if (b, q) /= (b', q')
       then throw $ CantConvert ltm rtm
       else do
         ty ~= ty'
         withDef d $ rhs ~= rhs'

  conv lhs@(App q f x) rhs@(App q' f' x') =
    if q /= q'
       then throw $ CantConvert lhs rhs
       else do
         f ~= f'
         x ~= x'

  conv Star Star = pure ()

  conv p q = throw $ CantConvert p q

  covering
  (~=) : TT Q n -> TT Q n -> TC n ()
  (~=) p q = conv (rnf p) (rnf q)

infixl 2 =<<
(=<<) : Monad m => (a -> m b) -> m a -> m b
(=<<) f x = x >>= f

covering
checkTm : Term n -> TC n (Ty n)
checkTm tm@(V i) = traceTm tm "VAR" $ use i *> lookup i
checkTm tm@(Bind Lam d@(D n q ty) rhs) = traceTm tm "LAM" $ do
  tyTy <- withQ E $ checkTm ty
  tyTy ~= Star

  Bind Pi d <$> (withDef d $ checkTm rhs)

checkTm tm@(Bind Pi d@(D n q ty) rhs) = traceTm tm "PI" $ do
  tyTy <- withQ E $ checkTm ty
  tyTy ~= Star

  withDef0 d $ do
    rhsTy <- checkTm rhs
    rhsTy ~= Star

  pure Star

checkTm tm@(App appQ f x) = traceTm tm "APP" $ do
  fTy <- rnf <$> checkTm f
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

covering
checkClosed : Term Z -> IO ()
checkClosed tm = case runTC (checkTm tm) (MkE L [] []) MkTCS of
    Left fail => printLn fail
    Right (MkTCS, [], ty) => putStrLn $ show tm ++ "\n  : " ++ show ty

example1 : TT Q Z
example1 =
  Bind Lam (D "a" I Star) $
  Bind Lam (D "x" L (V FZ)) $
  V FZ

namespace Main
  covering
  main : IO ()
  main = checkClosed example1
