module Inference.Elab

import public Core.Globals

import Core.TC
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

TC : Type -> Nat -> Type -> Type
TC q n a = Core.TC.TC Error (List (Equality q)) q n a

export
elab : Globals q -> Either Error (Globals q)
elab gs = ?rhs
