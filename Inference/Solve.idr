module Inference.Solve

import public Core.Quantity
import public Compiler.Config
import public Compiler.Monad
import public Inference.Evar
import public Inference.Infer
import public Inference.Constraint

import Inference.Quick
import Inference.SmtQuick
import Inference.SmtModel

import Data.Strings
import public Data.SortedMap

%default total
%undotted_record_projections off

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
    Config
    -> Int
    -> Globals Evar
    -> Constrs
    -> Inference.Infer.TCState
    -> ITT (SortedMap ENum Q)
iterConstrs cfg i gs cs st = do
  log $ "  -> iteration " ++ show i 
  vals <- liftIO (SmtQuick.solve cs.constrs) >>= \case
    Left (Unsatisfiable core) => do
      log ""
      banner "# Unsatisfiable core #"
      log . render "  " $ vcat core
      log ""
      throw "inconsistent constraints"
    Left (OtherError err) => throw err
    Right vals => pure vals

  case newlyReachableEqs vals cs.deferredEqs of
    ([], _) => do
      log $ "    -> No more equalities, fixed point reached.\n"
      pure vals

    (newEqs, waitingEqs) => do
      log $ unlines
        [ "    " ++ showTm ctx x ++ " ~ " ++ showTm ctx y
        | DeferEq g bt ctx x y <- newEqs
        ]

      case (traverse_ Infer.resumeEq newEqs).run (MkE [] gs [] []) st of
        Left fail => throw $ show fail
        Right (MkR st' cs' eqs' lu' gu' ()) => do
          -- we use waitingEqs (eqs from the previous iteration that have not been reached yet)
          -- and eqs' (eqs from this iteration)
          -- we drop eqs we have already reached and checked
          -- otherwise we'd loop forever in checking them again and again
          iterConstrs cfg (i+1) gs
            -- prepend for efficiency
            (MkConstrs (cs' ++ cs.constrs) (eqs' ++ waitingEqs))
            st'

covering export
solve : Config -> Globals Evar -> Constrs -> ITT (SortedMap ENum Q)
solve cfg gs cs = iterConstrs cfg 1 gs cs MkTCS
