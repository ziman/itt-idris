module ITT.Module

import public ITT.Core
import public ITT.Globals
import public Utils.Pretty
import ITT.Pretty

public export
record Module (q : Type) where
  constructor MkModule
  definitions : List (Def q)

export
ShowQ q => Pretty () (Module q) where
  pretty () (MkModule ds) = vcat $
    map (\d => pretty () d $$ text "") ds

export
ShowQ q => Show (Module q) where
  show = render "  " . pretty ()
