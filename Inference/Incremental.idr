module Inference.Incremental

import public Core.Globals
import public Core.Quantity
import public Inference.Evar
import public Compiler.Config
import public Compiler.Monad
import public Data.SortedMap

import Data.Maybe
import Utils.Pretty
import Inference.Infer
import Inference.Solve

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
  -> List (Definition Evar)
  -> ITT (SortedMap ENum Q, SortedMap Name (List (List Evar)))
inferDefs cfg gsSolved result [] = pure result
inferDefs cfg gsSolved (oldVals, oldGlobalUsage) (d :: ds) = do
  prd $ text "inferring " <++> (pretty () d)
  log ""

  (cs, eqs, newGlobalUsage) <-
    case (inferDefinition d).run (MkE [] (snoc gsSolved d) [] []) MkTCS of
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

  newVals <- Solve.solve cfg (MkConstrs cs eqs)
  let vals = mergeLeft newVals oldVals
  let dSolved = mapQ definitionQ (fillI vals) d

  prd . indent $ pretty () dSolved
  log ""

  inferDefs cfg (snoc gsSolved dSolved) (vals, merge newGlobalUsage oldGlobalUsage) ds

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
