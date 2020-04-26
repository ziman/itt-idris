module Core.Clause

import public Core.TT
import public Core.Pattern

%default total
%undotted_record_projections off

public export
record Clause (q : Type) where
  constructor MkClause
  n : Nat
  pi : Telescope q Z n
  lhs : Pat q n
  rhs : TT q n
