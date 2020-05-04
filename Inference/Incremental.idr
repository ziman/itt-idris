module Inference.Incremental

import public Core.Globals
import public Core.Quantity
import public Inference.Evar
import public Compiler.Config
import public Compiler.Monad
import public Data.SortedMap

import Data.Maybe
import Inference.Infer
import Inference.Solve

-- if known, fill in; otherwise leave unspecified
fill : SortedMap ENum Q -> Evar -> Evar
fill vals (QQ q) = QQ q
fill vals (EV i) = fromMaybe (EV i) (QQ <$> lookup i vals)

inferDefs :
     Config
  -> Globals Evar
  -> (SortedMap ENum Q, SortedMap Name (List (List Evar)))
  -> List (Definition Evar)
  -> ITT (SortedMap ENum Q, SortedMap Name (List (List Evar)))
inferDefs cfg gsSolved result [] = pure result
inferDefs cfg gsSolved (oldVals, oldGlobalUsage) (d :: ds) = do
  log $ "inferring " ++ show d.binding.name

  (cs, eqs, newGlobalUsage) <-
    case (inferDefinition d).run (MkE [] (snoc gsSolved d) [] []) MkTCS of
      Left err => throw $ show err
      Right (MkR st cs eqs lu gu ()) => pure (cs, eqs, gu)

  prd . indent $
    text "inferred constraints: "
    $$ indentBlock (map (pretty ()) cs)
    $$ text ""
    $$ text "deferred equalities: "
    $$ indentBlock (map (pretty ()) eqs)

  newVals <- Solve.solve cfg (MkConstrs cs eqs)
  let vals = mergeLeft newVals oldVals
  let dSolved = mapQ definitionQ (fill vals) d
  inferDefs cfg (snoc gsSolved dSolved) (vals, merge newGlobalUsage oldGlobalUsage) ds

mapGCs : SortedMap ENum Q -> SortedMap Name (List (List Evar)) -> SortedMap Name (List (List Evar))
mapGCs vals = map (map (map (fill vals)))

export
infer : Config -> Globals Evar -> ITT (SortedMap ENum Q)
infer cfg evarified = do
  -- normally, we'd toposort the definitions here
  -- but let's just assume they come in the right order in the file
  -- (this is always the case in Idris, for example, provided there's no mutual recursion)
  --
  -- TODO: mutual recursion
  let initialGlobalUsage = insert (UN "main") [[]] empty  -- used exactly once by the RTS
  (vals, globUsage) <- inferDefs cfg empty (empty, initialGlobalUsage) (toList evarified)

  -- globals constraints can be solved entirely separately
  -- per-definition stages filled in some bogus annotations on binders of definitions
  -- but we don't care, we'll just overwrite them with this solution
  globConstrs <- case toConstrs evarified $ mapGCs vals globUsage of
    Left n => throw $ "constraint for non-existent global: " ++ show n
    Right gcs => pure gcs
  gvals <- Solve.solve cfg (MkConstrs globConstrs [])

  -- gvals have priority on conflict
  pure (mergeLeft gvals vals)
