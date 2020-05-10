module Elab.Solve

import public Core.TT
import public Core.Quantity
import public Elab.Equality
import public Utils.DepSortedMap

import Elab.Check

public export
data Error = SomeError

export
solve : List Equality -> Either Solve.Error (DepSortedMap (MetaNum, Nat) (\(i,n) => TT (Maybe Q) n))
solve eqs = ?rhs
