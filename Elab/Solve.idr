module Elab.Solve

import public Core.TT
import public Core.Quantity
import public Elab.Equality
import public Data.SortedMap

import Core.TC
import Elab.Lens
import Elab.Check

import Control.Monad.Identity

%hide Syntax.PreorderReasoning.Generic.infixl.(~=)
%hide Syntax.PreorderReasoning.infixl.(~=)

public export
data Error
  = Impossible String
  | CantUnify Equality (Failure Check.Error)

export
Show Solve.Error where
  show (Impossible msg) = "impossible: " ++ msg
  show (CantUnify eq err) = show $
    text "can't unify: "
    $$ indent (pretty () eq)
    $$ text "because: "
    $$ indent (show err)

Term : Nat -> Type
Term = TT (Maybe Q)

Subst : Type
Subst = Lens.Subst (Maybe Q)

Uncertains : Type
Uncertains = SortedMap MetaNum (List (n ** Term n))

data Outcome : Type where
  Solved : MetaNum -> (n ** Term n) -> Outcome
  Progress : List Equality -> Outcome
  Unsolvable : Equality -> Failure Check.Error -> Outcome

substScope : MetaNum -> (n ** Term n) -> (n' ** Term n') -> (n' ** Term n')
substScope mn ntm (n' ** tm') = (n' ** substOne mlTm mn ntm tm')

substC : MetaNum -> (n ** Term n) -> Subst -> Subst
substC mn ntm = map (substScope mn ntm)

substU : MetaNum -> (n ** Term n) -> Uncertains -> Uncertains
substU mn ntm = map (map $ substScope mn ntm)

addCandidate : MetaNum -> (n ** Term n) -> Uncertains -> Uncertains
addCandidate mn ntm = merge (insert mn [ntm] empty)

solveOne : {n : Nat} -> Certainty -> Suspended (Maybe Q) n -> Term n -> Term n -> Outcome
solveOne c ts (Meta mn) rhs = Solved mn (_ ** rhs)
solveOne c ts lhs (Meta mn) = Solved mn (_ ** lhs)
solveOne c ts lhs rhs =
  case resume ts $ (lhs ~= rhs) c of
    Left e => Unsolvable (MkE c ts lhs rhs) e
    Right (MkR eqs ()) => Progress eqs

-- TODO: deal with uncertains properly
addU : Subst -> List (MetaNum, List (n ** Term n)) -> Subst
addU s us = s

covering
solveMany : Subst -> Uncertains -> List Equality -> Either Solve.Error Subst
solveMany s us [] = Right (addU s $ toList us)  -- add uncertains
solveMany s us (MkE {n} c ts lhs rhs :: eqs) =
  case solveOne c ts (substMany mlTm s lhs) (substMany mlTm s rhs) of
    Solved mn ntm => case c of
      Uncertain => solveMany s (addCandidate mn ntm us) eqs
      Certain =>
        solveMany
          (insert mn ntm $ substC mn ntm  s)
          (delete mn     $ substU mn ntm us)
          eqs
    Progress moreEqs => solveMany s us (moreEqs ++ eqs)
    Unsolvable eq err => case c of
      Certain => Left $ CantUnify eq err
      Uncertain => solveMany s us eqs  -- just skip it

covering export
solve : List Equality -> Either Solve.Error (Lens.Subst (Maybe Q))
solve = solveMany empty empty
