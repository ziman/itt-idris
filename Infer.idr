module Infer

import Utils
import public TT
import public Evar
import public OrdSemiring

import Data.Fin
import Data.SortedSet as Set

public export
Set : Type -> Type
Set = SortedSet

public export
Backtrace : Type
Backtrace = List String

public export
data Constr : Type where
  CEq : (v, w : Evar) -> Constr
  CLeq : (bt : Backtrace) -> (gs : Set Evar) -> (v : Evar) -> Constr
  CConv : (gs : Set Evar) -> (bt : Backtrace) -> (ctx : Context Evar n) -> (x, y : TT Evar n) -> Constr

export
Show Constr where
  show (CEq v w) = show v ++ " ~ " ++ show w
  show (CLeq bt gs v) = show (Set.toList gs) ++ " -> " ++ show v
  show (CConv gs bt ctx x y) = show (Set.toList gs) ++ " -> " ++ showTm ctx x ++ " ~ " ++ showTm ctx y

public export
Constrs : Type
Constrs = List Constr

public export
Term : Nat -> Type
Term = TT Evar

public export
Ty : Nat -> Type
Ty = TT Evar

public export
record TCState where
  constructor MkTCS

public export
data ErrorMessage : Nat -> Type where
  CantConvert : TT Evar n -> TT Evar n -> ErrorMessage n
  NotPi : Ty n -> ErrorMessage n

showEM : Context Evar n -> ErrorMessage n -> String
showEM ctx (CantConvert x y)
    = "can't convert: " ++ showTm ctx x ++ " with " ++ showTm ctx y
showEM ctx (NotPi x)
    = "not a pi: " ++ showTm ctx x

public export
record Failure where
  constructor MkF
  backtrace : Backtrace
  n : Nat
  context : Context Evar n
  errorMessage : ErrorMessage n

export
Show Failure where
  show (MkF bt _ ctx msg)
    = "With backtrace:\n" ++ unlines (map ("  " ++) bt) ++ showEM ctx msg

public export
record Env (n : Nat) where
  constructor MkE
  guards : Set Evar
  context : Context Evar n
  backtrace : Backtrace

public export
record TC (n : Nat) (a : Type) where
  constructor MkTC
  runTC : Env n -> TCState -> Either Failure (TCState, Constrs, a)

Functor (TC n) where
  map f (MkTC g) = MkTC $ \env, st => case g env st of
    Left fail => Left fail
    Right (st', cs, x) => Right (st', cs, f x)

Applicative (TC n) where
  pure x = MkTC $ \env, st => Right (st, [], x)
  (<*>) (MkTC f) (MkTC g) = MkTC $ \env, st =>
    case f env st of
        Left fail => Left fail
        Right (st', cs', f') => case g env st' of
            Left fail => Left fail
            Right (st'', cs'', x'') => Right (st'', cs' ++ cs'', f' x'')

Monad (TC n) where
  (>>=) (MkTC f) g = MkTC $ \env, st =>
    case f env st of
        Left fail => Left fail
        Right (st', cs, x) => case g x of
            MkTC h => case h env st' of
                Left fail => Left fail
                Right (st'', cs'', x'') => Right (st'', cs ++ cs'', x'')

getEnv : TC n (Env n)
getEnv = MkTC $ \env, st => Right (st, [], env)

getCtx : TC n (Context Evar n)
getCtx = context <$> getEnv

throw : ErrorMessage n -> TC n a
throw msg = MkTC $ \env, st
    => Left (MkF (backtrace env) _ (context env) msg)

withDef : Def Evar n -> TC (S n) a -> TC n a
withDef d@(D n q ty) (MkTC f) = MkTC $ \(MkE gs ctx bt), st
  => case f (MkE gs (d :: ctx) bt) st of
    Left fail => Left fail
    Right (st', cs, x) => Right (st', CLeq bt (Set.fromList [QQ I]) q :: cs, x)

withQ : Evar -> TC n a -> TC n a
withQ q (MkTC f) = MkTC $ \(MkE gs ctx bt), st => f (MkE (Set.insert q gs) ctx bt) st

use : Fin n -> TC n ()
use i = MkTC $ \(MkE gs ctx bt), st
    => Right (st, [CLeq bt gs (defQ $ lookupCtx i ctx)], ())

eqEvar : Evar -> Evar -> TC n ()
eqEvar p q = MkTC $ \env, st => Right (st, [CEq p q], ())

lookup : Fin n -> TC n (Ty n)
lookup i = defType . lookupCtx i <$> getCtx

trace : Show tr => tr -> TC n a -> TC n a
trace t (MkTC f) = MkTC $ \(MkE gs ctx bt), st
  => f (MkE gs ctx (show t :: bt)) st

traceTm : Show tr => Term n -> tr -> TC n a -> TC n a
traceTm tm t (MkTC f) = MkTC $ \(MkE gs ctx bt), st
  => let msg = show t ++ ": " ++ showTm ctx tm
      in f (MkE gs ctx (msg :: bt)) st

deferConv : Evar -> Term n -> Term n -> TC n ()
deferConv q x y = MkTC $ \(MkE gs ctx bt), st
  => Right (st, [CConv (Set.fromList [q]) bt ctx x y], ())

mutual
  infix 3 ~=
  covering export
  (~=) : Term n -> Term n -> TC n ()
  (~=) p q = conv (rnf p) (rnf q)

  conv : Term n -> Term n -> TC n ()
  conv (V i) (V j) with (finEq i j)
    | True  = pure ()
    | False = throw $ CantConvert (V i) (V j)
  conv l@(Bind b d@(D n q ty) rhs) r@(Bind b' d'@(D n' q' ty') rhs') =
    if (b /= b') || (q /= q')
      then throw $ CantConvert l r
      else do
        ty ~= ty'
        withDef d $ rhs ~= rhs'
  conv l@(App q f x) r@(App q' f' x') =
    if q /= q'
      then throw $ CantConvert l r
      else do
        f ~= f'
        deferConv q x x'
  conv Star Star = pure ()
  conv l r = throw $ CantConvert l r

covering export
inferTm : Term n -> TC n (Ty n)
inferTm tm@(V i) = traceTm tm "VAR" $ use i *> lookup i
inferTm tm@(Bind Lam d@(D n q ty) rhs) = traceTm tm "LAM" $ do
  tyTy <- withQ (QQ I) $ inferTm ty
  tyTy ~= Star

  Bind Pi d <$> (withDef d $ inferTm rhs)

inferTm tm@(Bind Pi d@(D n q ty) rhs) = traceTm tm "PI" $ do
  tyTy <- withQ (QQ I) $ inferTm ty
  tyTy ~= Star

  withDef d $ do
    rhsTy <- withQ (QQ I) $ inferTm rhs
    rhsTy ~= Star

  pure Star

inferTm tm@(App appQ f x) = traceTm tm "APP" $ do
  fTy <- rnf <$> inferTm f
  xTy <- inferTm x
  case fTy of
    Bind Pi d@(D piN piQ piTy) piRhs => do
      xTy ~= piTy
      eqEvar appQ piQ
      pure $ substVars (substTop x) piRhs

    _ => throw $ NotPi fTy

inferTm Star = pure Star
