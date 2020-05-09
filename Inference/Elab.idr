module Inference.Elab

import public Core.Globals

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

export
elab : Globals q -> Either Error (Globals q)
elab gs = ?rhs
