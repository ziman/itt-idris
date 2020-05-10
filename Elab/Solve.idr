module Elab.Solve

import public Core.TT
import public Core.Quantity
import public Elab.Equality
import public Utils.DepSortedMap

import Core.TC
import Elab.Check

public export
data Error
  = Impossible String
  | CantUnify Equality

export
Show Solve.Error where
  show (Impossible msg) = "impossible: " ++ msg
  show (CantUnify eq) = "can't unify: " ++ show (pretty () eq)

public export
Subst : Type
Subst = DepSortedMap (MetaNum, Nat) (\(mn,n) => TT (Maybe Q) n)

Term : Nat -> Type
Term = TT (Maybe Q)

data Outcome : Nat -> Type where
  Solved : MetaNum -> Term n -> Outcome n
  Progress : List Equality -> Outcome n
  Stuck : Equality -> Outcome n

Uncertains : Type
Uncertains = DepSortedMap (MetaNum, Nat) (\(mn,n) => List (Term n))

substC : MetaNum -> (n : Nat) -> Term n -> Subst -> Subst
substC mn n tm s = ?rhs_substC

substU : MetaNum -> (n : Nat) -> Term n -> Uncertains -> Uncertains
substU mn n tm us = ?rhs_substU

addCandidate : MetaNum -> (n : Nat) -> Term n -> Uncertains -> Uncertains
addCandidate mn n tm us = ?rhs_addCandidate

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
