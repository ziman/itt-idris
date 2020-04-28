module Inference.Infer

import Utils.Misc
import public Core.TT
import public Core.TT.Pretty
import public Core.Context
import public Core.Normalise
import public Inference.Evar
import public Utils.OrdSemiring

import Data.Fin
import Data.List
import Data.Strings
import Data.SortedSet

%default total

public export
Set : Type -> Type
Set = SortedSet

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
  CantInferErased : ErrorMessage n
  NotImplemented : ErrorMessage n
  QuantityMismatch : Q -> Q -> ErrorMessage n
  Debug : Doc -> ErrorMessage n

showEM : Context Evar n -> ErrorMessage n -> String
showEM ctx (CantConvert x y)
    = "can't convert: " ++ showTm ctx x ++ " with " ++ showTm ctx y
showEM ctx (NotPi x)
    = "not a pi: " ++ showTm ctx x
showEM ctx CantInferErased
    = "can't infer types for erased terms"
showEM ctx NotImplemented
    = "WIP: not implemented yet"
showEM ctx (QuantityMismatch q q')
    = "quantity mismatch: " ++ show q ++ " /= " ++ show q'
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
  context : Context Evar n
  errorMessage : ErrorMessage n

export
Show Failure where
  show (MkF bt _ ctx msg) = "With backtrace:\n"
    ++ unlines (reverse $ map ("  " ++) bt)
    ++ showEM ctx msg

public export
data Constr : Type where
  CEq : (v, w : Evar) -> Constr
  CLeq : (bt : Backtrace) -> (gs : SortedSet Evar) -> (v : Evar) -> Constr

public export
data DeferredEq : Type where
  DeferEq : (g : Evar) -> (bt : Backtrace)
    -> (ctx : Context Evar n) -> (x, y : TT Evar n) -> DeferredEq

export
Show Constr where
  show (CEq v w) = show v ++ " ~ " ++ show w
  show (CLeq bt gs v) = show (SortedSet.toList {k=Evar} gs) ++ " -> " ++ show v

export
Show DeferredEq where
  show (DeferEq g bt ctx x y) =
    show g ++ " -> " ++ showTm ctx x ++ " ~ " ++ showTm ctx y

public export
record Constrs where
  constructor MkConstrs
  constrs : List Constr
  deferredEqs : List DeferredEq

export
Semigroup Constrs where
  (<+>) (MkConstrs cs eqs) (MkConstrs cs' eqs')
    = MkConstrs (cs <+> cs') (eqs <+> eqs')

export
Monoid Constrs where
  neutral = MkConstrs [] []

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

export
Functor (TC n) where
  map f (MkTC g) = MkTC $ \env, st => case g env st of
    Left fail => Left fail
    Right (st', cs, x) => Right (st', cs, f x)

export
Applicative (TC n) where
  pure x = MkTC $ \env, st => Right (st, neutral, x)
  (<*>) (MkTC f) (MkTC g) = MkTC $ \env, st =>
    case f env st of
        Left fail => Left fail
        Right (st', cs', f') => case g env st' of
            Left fail => Left fail
            Right (st'', cs'', x'') => Right (st'', cs' <+> cs'', f' x'')

export
Monad (TC n) where
  (>>=) (MkTC f) g = MkTC $ \env, st =>
    case f env st of
        Left fail => Left fail
        Right (st', cs, x) => case g x of
            MkTC h => case h env st' of
                Left fail => Left fail
                Right (st'', cs'', x'') => Right (st'', cs <+> cs'', x'')

getEnv : TC n (Env n)
getEnv = MkTC $ \env, st => Right (st, neutral, env)

getCtx : TC n (Context Evar n)
getCtx = context <$> getEnv

throw : ErrorMessage n -> TC n a
throw msg = MkTC $ \env, st
    => Left (MkF (backtrace env) _ (context env) msg)

throwDebug : Doc -> TC n a
throwDebug = throw . Debug

withBnd : Binding Evar n -> TC (S n) a -> TC n a
withBnd b@(B n q ty) (MkTC f) = MkTC $ \(MkE gs ctx bt), st
  => case f (MkE gs (b :: ctx) bt) st of
    Left fail => Left fail
    Right (st', MkConstrs cs eqs, x)
        => Right (st', MkConstrs (CLeq bt (SortedSet.fromList [QQ I]) q :: cs) eqs, x)

withQ : Evar -> TC n a -> TC n a
withQ q (MkTC f) = MkTC $ \(MkE gs ctx bt), st
    => f (MkE (SortedSet.insert q gs) ctx bt) st

use : Fin n -> TC n ()
use i = MkTC $ \(MkE gs ctx bt), st
    => Right (st, MkConstrs [CLeq bt gs (bq $ lookup i ctx)] [], ())

useEvar : Evar -> TC n ()
useEvar ev = MkTC $ \(MkE gs ctx bt), st
    => Right (st, MkConstrs [CLeq bt gs ev] [], ())

eqEvar : Evar -> Evar -> TC n ()
eqEvar (QQ p) (QQ q) =
  if p == q
    then pure ()
    else throw $ QuantityMismatch p q
eqEvar p q = MkTC $ \env, st => Right (st, MkConstrs [CEq p q] [], ())

lookup : Fin n -> TC n (Ty n)
lookup i = bty . lookup i <$> getCtx

trace : Show tr => tr -> TC n a -> TC n a
trace t (MkTC f) = MkTC $ \(MkE gs ctx bt), st
  => f (MkE gs ctx (show t :: bt)) st

traceTm : Show tr => Term n -> tr -> TC n a -> TC n a
traceTm tm t (MkTC f) = MkTC $ \(MkE gs ctx bt), st
  => let msg = show t ++ ": " ++ showTm ctx tm
      in f (MkE gs ctx (msg :: bt)) st

deferEq : Evar -> Term n -> Term n -> TC n ()
deferEq g x y = MkTC $ \(MkE gs ctx bt), st
  => Right (st, MkConstrs [] [DeferEq g bt ctx x y], ())

mutual
  infix 3 ~=
  covering export
  (~=) : Term n -> Term n -> TC n ()
  (~=) p q = do
    conv (whnf p) (whnf q)

  covering
  conv : Term n -> Term n -> TC n ()
  conv (V i) (V j) = case finEq i j of
    True  => pure ()
    False => throw $ CantConvert (V i) (V j)

  conv l@(Lam b@(B n q ty) rhs) r@(Lam b'@(B n' q' ty') rhs') = do
    eqEvar q q'
    ty ~= ty'
    withBnd b $ rhs ~= rhs'

  conv l@(Pi b@(B n q ty) rhs) r@(Pi b'@(B n' q' ty') rhs') = do
    eqEvar q q'
    ty ~= ty'
    withBnd b $ rhs ~= rhs'

  conv l@(App q f x) r@(App q' f' x') = do
    eqEvar q q'
    f ~= f'
    case q of
      QQ I => pure ()
      QQ _ => x ~= x'
      EV _ => deferEq q x x'
  conv Star Star = pure ()
  conv Bool_ Bool_ = pure ()
  conv True_ True_ = pure ()
  conv False_ False_ = pure ()
  conv (If_ c t e) (If_ c' t' e') = do
    c ~= c'
    t ~= t'
    e ~= e'
  conv l r = throw $ CantConvert l r

covering export
resumeEq : DeferredEq -> TC n ()
resumeEq (DeferEq g bt ctx x y) = MkTC $ \env, st =>
  case x ~= y of
    MkTC f => f (MkE SortedSet.empty ctx bt) st

mutual
  covering export
  inferTm : Term n -> TC n (Ty n)
  inferTm tm@(V i) = traceTm tm "VAR" $ use i *> lookup i

  inferTm tm@(Lam b@(B n q ty) rhs) = traceTm tm "LAM" $ do
    tyTy <- withQ (QQ I) $ inferTm ty
    tyTy ~= Star

    Pi b <$> (withBnd b $ inferTm rhs)

  inferTm tm@(Pi b@(B n q ty) rhs) = traceTm tm "PI" $ do
    tyTy <- withQ (QQ I) $ inferTm ty
    tyTy ~= Star

    withBnd b $ do
      rhsTy <- withQ (QQ I) $ inferTm rhs
      rhsTy ~= Star

    pure Star

  inferTm tm@(App appQ f x) = traceTm tm "APP" $ do
    fTy <- whnf <$> inferTm f
    xTy <- inferTm x
    case fTy of
      Pi b@(B piN piQ piTy) piRhs => do
        traceTm fTy "fTy" $ xTy ~= piTy
        eqEvar appQ piQ
        pure $ subst (substFZ x) piRhs

      _ => throw $ NotPi fTy

  inferTm Star = pure Star
  inferTm Erased = throw CantInferErased

  inferTm Bool_ = pure Star
  inferTm True_ = pure Bool_
  inferTm False_ = pure Bool_
  inferTm (If_ c t e) = do
    cty <- inferTm c
    cty ~= Bool_

    tty <- inferTm t
    ety <- inferTm e
    tty ~= ety

    pure tty
