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
inferDefs cfg gs vals [] = pure vals
inferDefs cfg gs vals (d :: ds) = ?rhs

export
incrementalInference : Config -> Globals Evar -> ITT (SortedMap ENum Q)
incrementalInference cfg evarified =
  -- normally, we'd toposort the definitions here
  -- but let's just assume they come in the right order in the file
  -- (this is always the case in Idris, for example, provided there's no mutual recursion)
  --
  -- TODO: mutual recursion
  inferDefs cfg evarified empty $ toList evarified
