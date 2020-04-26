module Core.Clause

import public Core.TT
import public Core.Context
import public Core.Pattern

%default total
%undotted_record_projections off

public export
record Clause (q : Type) (argn : Nat) where
  constructor MkClause
  {pn : Nat}
  pi : Context q pn
  lhs : Vect argn (Pat q pn)
  rhs : TT q pn
