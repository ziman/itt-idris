module Compiler.Module

import ITT.Check
import ITT.Erase
import ITT.Normalise
import public ITT.Core
import public ITT.Module
import public Compiler.Monad

import Inference.Evar
import Inference.Infer
import Inference.SmtModel

import Data.SortedSet as Set
import Data.SortedMap as Map

%default total

banner : String -> ITT ()
banner s = log hrule *> log s *> log hrule *> log ""
  where
    hrule = pack $ List.replicate (length s) '#'

isRelevant : SortedMap ENum Q -> Evar -> Maybe Bool
isRelevant vs (QQ I) = Just False
isRelevant vs (QQ _) = Just True
isRelevant vs (EV i) = case Map.lookup i vs of
  Nothing => Nothing  -- we don't know yet
  Just I  => Just False
  Just _  => Just True

newlyReachableEqs : SortedMap ENum Q -> List DeferredEq
    -> (List DeferredEq, List DeferredEq)
newlyReachableEqs vs [] = ([], [])
newlyReachableEqs vs (eq@(DeferEq g _ _ _ _ _) :: eqs) =
  let (reached, unknown) = newlyReachableEqs vs eqs
    in case isRelevant vs g of
      Nothing => (reached, eq :: unknown)    -- still unknown
      Just True => (eq :: reached, unknown)  -- newly reached!
      Just False => (reached, unknown)       -- definitely unreachable, drop it

covering
iterConstrs : Int
    -> Constrs
    -> Globals Evar
    -> Infer.TCState
    -> ITT (SortedMap ENum Q)
iterConstrs i (MkConstrs cs eqs) glob st = do
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
        | DeferEq g bt glob ctx x y <- newEqs
        ]

      case Infer.TC.runTC (traverse_ resumeEq newEqs) (MkE Set.empty [] [] glob) st of
        Left fail => throw $ show fail
        Right (st', MkConstrs cs' eqs', ()) => do
          -- we use waitingEqs (eqs from the previous iteration that have not been reached yet)
          -- and eqs' (eqs from this iteration)
          -- we drop eqs we have already reached and checked
          -- otherwise we'd loop forever in checking them again and again
          iterConstrs (i+1)
            (MkConstrs (cs <+> cs') (waitingEqs <+> eqs'))
            glob
            st'

substQ : SortedMap ENum Q -> Evar -> Maybe Q
substQ vs (QQ q) = Just q
substQ vs (EV i) = Map.lookup i vs

covering export
processModule : Module (Maybe Q) -> ITT ()
processModule raw = do
  banner "# Desugared #"
  prn raw

  banner "# Evarified #"
  let evarified = evarify moduleQ raw
  prn evarified

  log "Running erasure inference..."
  cs <- case runTC (inferDefs $ definitions evarified) (MkE Set.empty [] [] Map.empty) MkTCS of
    Left err => throw $ show err
    Right (st, cs, ()) => pure cs

  banner "# Inferred constraints #"
  log $ unlines $ map show (constrs cs)

  banner "# Deferred equalities #"
  log $ unlines $ map show (deferredEqs cs)

  vals <- iterConstrs 1 cs (toGlobals evarified) MkTCS

  banner "# Final valuation #"
  log $ unlines
    [ "  " ++ show i ++ " -> " ++ show q
    | (i, q) <- Map.toList vals
    ]

  annotated <- case moduleQ (substQ vals) evarified of
    Nothing => throw "did not solve all evars"
    Just mod => pure mod

  banner "# Annotated program #"
  prn annotated

  banner "# Final check #"
  case Check.TC.runTC (checkDefs $ definitions annotated) (MkE L [] [] Map.empty) MkTCS of
    Left err => throw $ show err
    Right (MkTCS, [], ()) => log "OK\n"

  banner "# Erased #"
  let erased = eraseModule annotated
  prn erased
  
  banner "# WHNF #"
  log . render " "
    $ text "Unerased, reduced:"
    $$ pretty () (whnf (toGlobals annotated) (G $ N "main" 0))
    $$ text ""
    $$ text "Erased, reduced:"
    $$ pretty () (whnf (toGlobals erased) (G $ N "main" 0))
