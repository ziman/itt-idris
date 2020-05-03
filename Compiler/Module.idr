module Compiler.Module

import Core.Check
import Core.Erase
import Core.Normalise
import Core.TT.Pretty
import Core.Quantity
import public Core.TT
import public Compiler.Monad
import public Compiler.Config

import Inference.Evar
import Inference.Infer
import Inference.Solve
import Inference.Quick
import Inference.Constraint
import Inference.SmtModel

import Transformation.PruneClauses
import Transformation.DefaultCtorQuantities

import Data.List
import Data.Strings
import Data.SortedSet
import Data.SortedMap

%default total
%undotted_record_projections off

covering export
processModule : Config -> Globals (Maybe Q) -> ITT ()
processModule cfg raw = do
  banner "# Desugared #"
  printP () raw

  let rawCQ =
        if cfg.defaultConstructorQuantities
          then applyDefaultCtorQuantities raw
          else raw

  banner "# Evarified #"
  let evarified = evarify globalsQ rawCQ
  prn evarified

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

  -- solve the constraints
  vals <- Quick.solve cfg evarified cs

  banner "# Final valuation #"
  log $ unlines
    [ "  " ++ show i ++ " -> " ++ show q
    | (i, q) <- SortedMap.toList vals
    ]

  annotated <- case the (Maybe (Globals Q)) $ globalsQ (substQ vals) evarified of
    Nothing => throw "did not solve all evars"
    Just gs => pure gs

  banner "# Annotated program #"
  prn annotated

  {-
  banner "# Final check #"
  case checkGlobals.run (MkE L annotated [] []) MkTCS of
    Left err => throw $ show err
    Right (MkTCS, usage, ()) => do
      log "** OK **\n"
  -}

  banner "# Erased #"
  let erased = eraseGlobals $
        if cfg.pruneClauses
          then PruneClauses.pruneGlobals annotated
          else annotated
  prn erased

  banner "# NF of `main` #"

  log . render " "
    $ text "Unerased, reduced:"
    $$ case red NF annotated (P (UN "main")) of
        Left e => text $ show e
        Right mnf => pretty () (the (TT Q Z) mnf)
    $$ text ""
    $$ text "Erased, reduced:"
    $$ case red NF erased (P (UN "main")) of
        Left e => text $ show e
        Right mnf => pretty () (the (TT () Z) mnf)
