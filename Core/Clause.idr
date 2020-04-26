module Core.Clause

import public Core.TT
import public Core.Pattern

%default total
%undotted_record_projections off

public export
record Clause (q : Type) (argn : Nat) where
  constructor MkClause
  n : Nat
  pi : Telescope q Z n
  lhs : Vect argn (Pat q n)
  rhs : TT q n
