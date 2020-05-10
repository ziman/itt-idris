module Compiler.Module

import Core.Check
import Core.Erase
import Core.Normalise
import Core.TT.Pretty
import Core.Quantity
import public Core.Pragma
import public Core.TT
import public Compiler.Monad
import public Compiler.Config

import Elab.Core
import Elab.Lens
import Elab.Check
import Elab.Solve
import Elab.Equality

import Inference.Incremental
import Inference.WholeProgram

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

  banner "# Elaboration #"
  let numbered = numberMetas rawCQ
  prn numbered

  eqs <- case gatherEqualities numbered of
    Left e => throw $ "could not gather equalities: " ++ show e
    Right eqs => pure eqs

  log ""
  log "Equalities:"
  prn $ indentBlock (map (pretty ()) eqs)

  solution <- case solve eqs of
    Left e => throw $ "could not solve equalities: " ++ show e
    Right s => pure s

  banner "# Elaborated #"
  let elaborated = fill solution numbered
  prn elaborated

  banner "# Evarified #"
  let evarified = evarify globalsQ elaborated
  prn evarified

  vals <- case cfg.incrementalInference of
    True => Incremental.infer cfg evarified
    False => WholeProgram.infer cfg evarified

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

  pruned <- case cfg.pruneClauses of
    False => pure annotated
    True => do
      log ""
      banner "# Pruned #"
      let pruned = PruneClauses.pruneGlobals annotated
      prn pruned
      pure pruned

  banner "# Erased #"
  let erased = eraseGlobals pruned
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
