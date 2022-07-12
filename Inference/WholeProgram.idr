module Inference.WholeProgram

import public Core.Globals
import public Core.Quantity
import public Compiler.Config
import public Compiler.Monad
import public Inference.Evar
import public Inference.Infer
import public Inference.Variance
import public Inference.Constraint
import public Data.SortedMap

import Data.String
import Inference.Solve
import Data.SortedSet

export
infer : Config -> Globals Evar -> ITT (SortedMap ENum Q)
infer cfg evarified = do
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

  banner "# Variance of evars #"
  let var = concatMap (concatMap $ variance . type . binding) $ toBlocks evarified
  prd $ pretty () var

  -- globals are not really bound contravariantly
  -- and this would be wrong in separate compilation
  -- but we want to maximise their erasure so let's mark them like contravariant
  let qGlobals = concatMap (concatMap $ getENum . qv . binding) $ toBlocks evarified

  Solve.solve cfg (var.contravariant <+> qGlobals) var.covariant cs
