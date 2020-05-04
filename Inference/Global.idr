module Inference.Global

import public Core.Globals
import public Core.Quantity
import public Compiler.Config
import public Compiler.Monad
import public Inference.Evar
import public Inference.Infer
import public Inference.Constraint
import public Data.SortedMap

import Data.Strings
import Inference.Solve

export
globalInference : Config -> Globals Evar -> ITT (SortedMap ENum Q)
globalInference cfg evarified = do
  log "Running erasure inference...\n"
  cs <- case inferGlobals.run (MkE [] evarified [] []) MkTCS of
    Left err => throw $ show err
    Right (MkR st cs eqs lu gu ()) =>
      case toConstrs evarified $ addMain gu of
        Left n => throw $ "constraint for non-existent global: " ++ show n
        Right gcs => pure $ MkConstrs (gcs ++ cs) eqs

  banner "# Inferred constraints #"
  prd $ vcat (map (pretty ()) cs.constrs)

  banner "# Deferred equalities #"
  log $ unlines $ map show cs.deferredEqs

  Solve.solve cfg cs
