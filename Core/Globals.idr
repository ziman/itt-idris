module Core.Globals

import public Core.Clause
import Data.SortedMap

%default total
%undotted_record_projections off

public export
data Definition : (q : Type) -> Type where
  Postulate : Definition q
  Foreign : String -> Definition q
  Clauses : List (Clause q) -> Definition q

export
record Globals (q : Type) where
  constructor MkGlobals
  byName : SortedMap Name (Definition q)
