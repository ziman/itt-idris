module Inference.Elab

import public Core.Globals

import Inference.Constraint
import Control.Monad.State

%default total
%undotted_record_projections off

public export
data Error
  = NotImplementedYet
  | OtherError String

export
Show Error where
  show NotImplementedYet = "not implemented yet"
  show (OtherError msg) = "error: " ++ msg

record Equality (q : Type) where
  constructor MkE
  {0 n : Nat}
  lhs : TT q n
  rhs : TT q n

record Env (q : Type) (n : Nat) where
  constructor MkTS
  globals : Globals q
  context : Context q n

record TCResult (q : Type) (n : Nat) (a : Type) where
  constructor MkR
  eqs : List (Equality q)
  value : a

Functor (TCResult q n) where
  map f (MkR eqs x) = MkR eqs (f x)

Applicative (TCResult q n) where
  pure x = MkR [] x
  MkR eqs f <*> MkR eqs' x = MkR (eqs <+> eqs') (f x)

record TC (q : Type) (n : Nat) (a : Type) where
  constructor MkTC
  run : Env q n -> Either Error (TCResult q n a)

Functor (TC q n) where
  map f (MkTC g) = MkTC $ \env => map f <$> g env

Applicative (TC q n) where
  pure x = MkTC $ \env => pure (pure x)
  MkTC f <*> MkTC g = MkTC $ \env => [| f env <*> g env |]

Monad (TC q n) where
  (>>=) (MkTC f) g = MkTC $ \env => do
    MkR eqs  x <- f env
    MkR eqs' y <- (g x).run env
    pure $ MkR (eqs <+> eqs') y

export
elab : Globals q -> Either Error (Globals q)
elab gs = ?rhs
