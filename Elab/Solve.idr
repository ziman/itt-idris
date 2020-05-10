module Elab.Solve

import public Core.TT
import public Core.Quantity
import public Elab.Equality
import public Utils.DepSortedMap

import Core.TC
import Elab.Lens
import Elab.Check

import Control.Monad.Identity

public export
data Error
  = Impossible String
  | CantUnify Equality

export
Show Solve.Error where
  show (Impossible msg) = "impossible: " ++ msg
  show (CantUnify eq) = "can't unify: " ++ show (pretty () eq)

Term : Nat -> Type
Term = TT (Maybe Q)

public export
Subst : Type
Subst = DepSortedMap (MetaNum, Nat) (\mnn => Term (snd mnn))

Uncertains : Type
Uncertains = DepSortedMap (MetaNum, Nat) (\mnn => List (Term (snd mnn)))

data Outcome : Nat -> Type where
  Solved : MetaNum -> Term n -> Outcome n
  Progress : List Equality -> Outcome n
  Stuck : Equality -> Outcome n

substC : MetaNum -> (n : Nat) -> Term n -> Subst -> Subst
substC mn n tm = map (subst mlTm mn n tm)

substU : MetaNum -> (n : Nat) -> Term n -> Uncertains -> Uncertains
substU mn n tm = map (map $ subst mlTm mn n tm)

addCandidate : MetaNum -> (n : Nat) -> Term n -> Uncertains -> Uncertains
addCandidate mn n tm = insertWith (mn, n) $ \case
  Nothing => [tm]
  Just tms => tm :: tms

solveOne : Certainty -> Suspended (Maybe Q) n -> Term n -> Term n -> Outcome n
solveOne c ts lhs rhs = ?rhs_solveOne

covering
solveMany : Subst -> Uncertains -> List Equality -> Either Solve.Error Subst
solveMany s us [] = Right s
solveMany s us (MkE {n} c ts lhs rhs :: eqs) =
  case solveOne c ts lhs rhs of
    Solved mn tm => case c of
      Uncertain => solveMany s (addCandidate mn n tm us) eqs
      Certain =>
        solveMany
          (insert (mn, n)  tm  $ substC mn n tm  s)
          (delete (mn, n)      $ substU mn n tm us)
          eqs
    Progress moreEqs => solveMany s us (moreEqs ++ eqs)
    Stuck eq => Left $ CantUnify eq

covering export
solve : List Equality -> Either Solve.Error Subst
solve = solveMany empty empty
