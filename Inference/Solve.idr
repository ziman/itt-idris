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

import Data.String
import public Data.SortedSet
import public Data.SortedMap

%default total

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
newlyReachableEqs vs (eq@(DeferEq trigger _ _ _ _ _) :: eqs) =
  let (reached, unknown) = newlyReachableEqs vs eqs
    in case isRelevant vs trigger of
      Nothing => (reached, eq :: unknown)    -- still unknown
      Just True => (eq :: reached, unknown)  -- newly reached!
      Just False => (reached, unknown)       -- definitely unreachable, drop it

covering
iterConstrs :
    Config
    -> Int
    -> SortedSet ENum
    -> SortedSet ENum
    -> Constrs
    -> Inference.Infer.TCState
    -> ITT (SortedMap ENum Q)
iterConstrs cfg i minvs maxvs cs st = do
  vals <- liftIO (SmtModel.solve minvs maxvs cs.constrs) >>= \case
    Left (Unsatisfiable core) => do
      log ""
      banner "# Unsatisfiable core #"
      log . render "  " $ vcat core
      log ""
      throw "inconsistent constraints"
    Left (OtherError err) => throw err
    Right vals => pure vals

  case newlyReachableEqs vals cs.deferredEqs of
    ([], _) => pure vals

    (newEqs, waitingEqs) => do
      log $ "  -> iteration " ++ show i
      log $ unlines
        [ "    " ++ showTm ctx x ++ " ~ " ++ showTm ctx y
        | DeferEq trigger bt gs ctx x y <- newEqs
        ]

      case (traverse_ Infer.resumeEq newEqs).run (MkE [] empty [] []) st of
        Left fail => throw $ show fail
        Right (MkR st' cs' eqs' lu' gu' ()) => do
          -- we use waitingEqs (eqs from the previous iteration that have not been reached yet)
          -- and eqs' (eqs from this iteration)
          -- we drop eqs we have already reached and checked
          -- otherwise we'd loop forever in checking them again and again
          iterConstrs cfg (i+1) minvs maxvs
            -- prepend for efficiency
            (MkConstrs (cs' ++ cs.constrs) (eqs' ++ waitingEqs))
            st'

covering export
solve : Config -> SortedSet ENum -> SortedSet ENum -> Constrs -> ITT (SortedMap ENum Q)
solve cfg minvs maxvs cs = iterConstrs cfg 1 minvs maxvs cs MkTCS
