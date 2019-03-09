module ITT.Globals

import public ITT.Core
import Data.SortedMap

public export
data Body : (q : Type) -> Type where
  Abstract : Body q     -- postulates, primitives, ..., not a value
  Constructor : Body q  -- is a value
  Term : TT q Z -> Body q

public export
record Def (q : Type) where
  constructor D
  dn  : Name
  dq  : q
  dty : TT q Z
  db  : Body q

export
Globals : (q : Type) -> Type
Globals q = SortedMap Name (Def q)

export
lookup : Name -> Globals q -> Maybe (Def q)
lookup = SortedMap.lookup
