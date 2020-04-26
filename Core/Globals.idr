module Core.Globals

import public Core.TT
import public Core.Clause
import Data.SortedMap

%default total
%undotted_record_projections off

public export
data Body : (q : Type) -> Type where
  Postulate : Body q
  Constructor : Body q
  Foreign : String -> Body q
  Clauses : (argn : Nat) -> List (Clause q argn) -> Body q

public export
record Definition (q : Type) where
  constructor MkDef
  binding : Binding q Z
  body : Body q

export
record Globals (q : Type) where
  constructor MkGlobals
  definitions : SortedMap Name (Definition q)

export
lookup : Name -> Globals q -> Maybe (Definition q)
lookup n gs = lookup n gs.definitions

export
toGlobals : List (Definition q) -> Globals q
toGlobals ds =
  MkGlobals $ SortedMap.fromList
    [(UN d.binding.name, d) | d <- ds]
