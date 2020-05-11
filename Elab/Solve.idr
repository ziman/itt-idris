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
Uncertains = DepSortedMap (MetaNum, Nat) (\mnn => List (Term (snd mnn)))

data Outcome : Type where
  Solved : MetaNum -> (n' ** Term n') -> Outcome
  Progress : List Equality -> Outcome
  Stuck : Equality -> Failure Check.Error -> Outcome

substC : MetaNum -> (n : Nat) -> Term n -> Subst -> Subst
substC mn n tm = map (subst mlTm mn n tm)

substU : MetaNum -> (n : Nat) -> Term n -> Uncertains -> Uncertains
substU mn n tm = map (map $ subst mlTm mn n tm)

addCandidate : MetaNum -> (n : Nat) -> Term n -> Uncertains -> Uncertains
addCandidate mn n tm = insertWith (mn, n) $ \case
  Nothing => [tm]
  Just tms => tm :: tms

solveOne : {n : Nat} -> Certainty -> Suspended (Maybe Q) n -> Term n -> Term n -> Outcome
solveOne c ts (Meta mn) rhs = Solved mn (strengthenMax _ rhs)
solveOne c ts lhs (Meta mn) = Solved mn (strengthenMax _ lhs)
solveOne c ts lhs rhs =
  case resume {q = Maybe Q} {w = List Equality} ts $ (lhs ~= rhs) c of
    Left e => Stuck (MkE c ts lhs rhs) e
    Right (MkR eqs ()) => Progress eqs

-- TODO: deal with uncertains properly
addU : Subst -> List (mnn ** List (Term $ Builtin.snd mnn)) -> Subst
addU s us = s
{-
addU s (((mn, n) ** [tm]) :: xs) = addU (insert (mn, n) tm s) xs -- only one solution, just use it
addU s (((mn, n) ** tm) :: xs) = addU s xs
-}

covering
solveMany : Subst -> Uncertains -> List Equality -> Either Solve.Error Subst
solveMany s us [] = Right (addU s $ toList us)
solveMany s us (MkE {n} c ts lhs rhs :: eqs) =
  case solveOne c ts (substMany mlTm s lhs) (substMany mlTm s rhs) of
    Solved mn (n' ** tm') => case c of
      Uncertain => solveMany s (addCandidate mn n' tm' us) eqs
      Certain =>
        solveMany
          (insert (mn, n')  tm'  $ substC mn n' tm'  s)
          (delete (mn, n')       $ substU mn n' tm' us)
          eqs
    Progress moreEqs => solveMany s us (moreEqs ++ eqs)
    Stuck eq err => Left $ CantUnify eq err

covering export
solve : List Equality -> Either Solve.Error (Lens.Subst (Maybe Q))
solve = solveMany empty empty
