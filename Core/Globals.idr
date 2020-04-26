module Core.Globals

import public Core.Clause
import Data.SortedMap

%default total
%undotted_record_projections off

public export
data Definition : (q : Type) -> Type where
  Postulate : Definition q
  Constructor : Definition q
  Foreign : String -> Definition q
  Clauses : (argn : Nat) -> List (Clause q argn) -> Definition q

export
record Globals (q : Type) where
  constructor MkGlobals
  byName : SortedMap Name (Definition q)

export
lookup : Name -> Globals q -> Maybe (Definition q)
lookup n gs = SortedMap.lookup n gs.byName
