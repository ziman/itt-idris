module Inference.Incremental

import public Core.Globals
import public Core.Quantity
import public Inference.Evar
import public Compiler.Config
import public Compiler.Monad
import public Data.SortedMap

import Data.Maybe

import Core.TT.Utils
import Inference.Infer
import Inference.Solve
import Inference.Variance
import Utils.Pretty

-- fill/conservative
-- if known, fill in; otherwise leave unspecified
fillC : SortedMap ENum Q -> Evar -> Evar
fillC vals (QQ q) = QQ q
fillC vals (EV i) = fromMaybe (EV i) (QQ <$> lookup i vals)

-- fill/I
fillI : SortedMap ENum Q -> Evar -> Evar
fillI vals (QQ q) = QQ q
fillI vals (EV i) = fromMaybe (QQ I) (QQ <$> lookup i vals)

inferDefs :
     Config
  -> Globals Evar
  -> (SortedMap ENum Q, SortedMap Name (List (List Evar)))
  -> List (List (Definition Evar))
  -> ITT (SortedMap ENum Q, SortedMap Name (List (List Evar)))
inferDefs cfg gsSolved result [] = pure result
inferDefs cfg gsSolved (oldVals, oldGlobalUsage) (ds :: dss) = do
  prd $ text "inferring " <++> (pretty () ds)
  log ""

  (cs, eqs, newGlobalUsage) <-
    case (traverse_ inferDefinition ds).run (MkE [] (gsSolved `snocBlock` ds) [] []) MkTCS of
      Left err => throw $ show err
      Right (MkR st cs eqs lu gu ()) => pure (cs, eqs, gu)

  prd . indent $
    (case cs of
        [] => neutral
        _ =>
          text "inferred constraints: "
          $$ indentBlock (map (pretty ()) cs)
          $$ text ""
    ) $$ (
      case eqs of
        [] => neutral
        _ =>
          text "deferred equalities: "
          $$ indentBlock (map (pretty ()) eqs)
          $$ text ""
    )

  log "  variance of evars:"
  let var = concatMap (variance . .binding.type) ds
  prd . indent $
    text "variance of evars:"
    $$ indent (pretty () var)

  newVals <- Solve.solve cfg var.contravariant var.covariant (MkConstrs cs eqs)
  let vals = mergeLeft newVals oldVals
  let dsSolved = map (mapQ definitionQ (fillI vals)) ds

  prd . indent $ pretty () dsSolved
  log ""

  inferDefs cfg (snocBlock gsSolved dsSolved) (vals, merge newGlobalUsage oldGlobalUsage) dss

mapGCs : SortedMap ENum Q -> SortedMap Name (List (List Evar)) -> SortedMap Name (List (List Evar))
mapGCs vals = map (map (map (fillC vals)))

export
infer : Config -> Globals Evar -> ITT (SortedMap ENum Q)
infer cfg evarified = do
  -- normally, we'd toposort the definitions here
  -- but let's just assume they come in the right order in the file
  -- (this is always the case in Idris, for example, provided there's no mutual recursion)
  --
  -- TODO: mutual recursion
  let initialGlobalUsage = insert (UN "main") [[]] empty  -- used exactly once by the RTS
  (vals, globUsage) <- inferDefs cfg empty (empty, initialGlobalUsage) (toBlocks evarified)

  -- globals constraints can be solved entirely separately
  -- per-definition stages filled in some bogus annotations on binders of definitions
  -- but we don't care, we'll just overwrite them with this solution
  globConstrs <- case toConstrs evarified $ mapGCs vals globUsage of
    Left n => throw $ "constraint for non-existent global: " ++ show n
    Right gcs => pure gcs

  let allGVs = concat [concatMap (getENum . .binding.qv) ds | ds <- toBlocks evarified]
  gvals <- Solve.solve cfg allGVs empty (MkConstrs globConstrs [])

  -- gvals have priority on conflict
  pure (mergeLeft gvals vals)
