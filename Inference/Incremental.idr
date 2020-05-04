module Inference.Incremental

import public Core.Globals
import public Core.Quantity
import public Inference.Evar
import public Compiler.Config
import public Compiler.Monad
import public Data.SortedMap

inferDefs : Config -> Globals Evar
  -> SortedMap ENum Q
  -> List (Definition Evar)
  -> ITT (SortedMap ENum Q)
inferDefs cfg gs vals ds = ?rhs

export
incrementalInference : Config -> Globals Evar -> ITT (SortedMap ENum Q)
incrementalInference cfg evarified =
  inferDefs cfg evarified empty $ toList evarified
