module Compiler.Module

import Core.Check
import Core.Erase
import Core.Normalise
import Core.TT.Pretty
import Core.Quantity
import public Core.TT
import public Compiler.Monad

import Inference.Evar
import Inference.Infer
import Inference.Constraint
import Inference.SmtModel

import Data.List
import Data.Strings
import Data.SortedSet
import Data.SortedMap

%default total

banner : String -> ITT ()
banner s = log hrule *> log s *> log hrule *> log ""
  where
    hrule : String
    hrule = pack $ List.replicate (length s) '#'

isRelevant : SortedMap ENum Q -> Evar -> Maybe Bool
isRelevant vs (QQ I) = Just False
isRelevant vs (QQ _) = Just True
isRelevant vs (EV i) = case SortedMap.lookup i vs of
  Nothing => Nothing  -- we don't know yet
  Just I  => Just False
  Just _  => Just True

newlyReachableEqs : SortedMap ENum Q -> List DeferredEq
    -> (List DeferredEq, List DeferredEq)
newlyReachableEqs vs [] = ([], [])
newlyReachableEqs vs (eq@(DeferEq g _ _ _ _) :: eqs) =
  let (reached, unknown) = newlyReachableEqs vs eqs
    in case isRelevant vs g of
      Nothing => (reached, eq :: unknown)    -- still unknown
      Just True => (eq :: reached, unknown)  -- newly reached!
      Just False => (reached, unknown)       -- definitely unreachable, drop it

covering
iterConstrs :
    Int
    -> Globals Evar
    -> Constrs
    -> Inference.Infer.TCState
    -> ITT (SortedMap ENum Q)
iterConstrs i gs (MkConstrs cs eqs) st = do
  log $ "  -> iteration " ++ show i 
  solution <- liftIO $ SmtModel.solve cs
  vals <- case solution of
    Left err => throw err
    Right vals => pure vals

  case newlyReachableEqs vals eqs of
    ([], _) => do
      log $ "    -> No more equalities, fixed point reached.\n"
      pure vals

    (newEqs, waitingEqs) => do
      log $ unlines
        [ "    " ++ showTm ctx x ++ " ~ " ++ showTm ctx y
        | DeferEq g bt ctx x y <- newEqs
        ]

      case (traverse_ Infer.resumeEq newEqs).run (MkE SortedSet.empty gs [] []) st of
        Left fail => throw $ show fail
        Right (st', MkConstrs cs' eqs', ()) => do
          -- we use waitingEqs (eqs from the previous iteration that have not been reached yet)
          -- and eqs' (eqs from this iteration)
          -- we drop eqs we have already reached and checked
          -- otherwise we'd loop forever in checking them again and again
          iterConstrs (i+1) gs
            (MkConstrs (cs <+> cs') (waitingEqs <+> eqs'))
            st'

substQ : SortedMap ENum Q -> Evar -> Maybe Q
substQ vs (QQ q) = Just q
substQ vs (EV i) = SortedMap.lookup i vs <|> Just I
-- sometimes, the solver does not return any solution for some variables
-- i assume that in such cases you can freely choose what you like
-- so we choose "I" here, by appending "<|> Just I"
-- this function thus never returns Nothing

covering export
processModule : Globals (Maybe Q) -> ITT ()
processModule raw = do
  banner "# Desugared #"
  printP () raw

  banner "# Evarified #"
  let evarified = evarify globalsQ raw
  prn evarified

  log "Running erasure inference..."
  cs <- case inferGlobals.run (MkE SortedSet.empty evarified [] []) MkTCS of
    Left err => throw $ show err
    Right (st, cs, ()) => pure cs

  banner "# Inferred constraints #"
  printP () $ collect cs.constrs

  banner "# Deferred equalities #"
  log $ unlines $ map show cs.deferredEqs

  vals <- iterConstrs 1 evarified cs MkTCS

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

  banner "# Final check #"
  case checkGlobals.run (MkE L annotated [] []) MkTCS of
    Left err => throw $ show err
    Right (MkTCS, usage, ()) => do
      log "\n** OK **\n"

  banner "# Erased #"
  let erased = eraseGlobals annotated
  prn erased

  banner "# WHNF of `main` #"

  log . render " "
    $ text "Unerased, reduced:"
    $$ case whnf annotated (P (UN "main")) of
        Left e => text $ show e
        Right nf => pretty () (the (TT Q Z) nf)
    $$ text ""
    $$ text "Erased, reduced:"
    $$ case whnf erased (P (UN "main")) of
        Left e => text $ show e
        Right nf => pretty () (the (TT () Z) nf)
