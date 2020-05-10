module Elab.Solve

import public Core.TT
import public Core.Quantity
import public Elab.Equality
import public Utils.DepSortedMap

import Core.TC
import Elab.Check

public export
data Error
  = MultipleSolutions MetaNum

export
Show Solve.Error where
  show (MultipleSolutions mn) = "multiple solutions for " ++ show mn

public export
Subst : Type
Subst = DepSortedMap (MetaNum, Nat) (\(mn,n) => TT (Maybe Q) n)

Term : Nat -> Type
Term = TT (Maybe Q)

data Solution : Nat -> Type where
  Unique : Term n -> Solution n
  Conflict : Solution n

Uncertains : Type
Uncertains = DepSortedMap (MetaNum, Nat) (\(mn,n) => Solution n)

solveOne : Certainty -> Term n -> Term n -> Either (MetaNum, Term n) (List Equality)
solveOne c lhs rhs = ?rhs_solveOne

covering
solveMany : Subst -> Uncertains -> List Equality -> Either Solve.Error Subst
solveMany s us [] = Right s
solveMany s us (MkE {n} c ctx lhs rhs :: eqs) =
  case solveOne c lhs rhs of
    Left (mn, tm) => case c of
      Certain => case lookup (mn, n) s of
        Just _ => Left $ MultipleSolutions mn
        Nothing =>
          solveMany
            (insert (mn, n) tm s)
            (insert (mn, n) Conflict us)  -- let's ignore uncertains because we have a certain solution
            eqs
      Uncertain => case lookup (mn, n) us of
        Just Conflict => solveMany s us eqs  -- nothing to do here
        Just (Unique tm') =>
          if tm' == tm
            then solveMany s us eqs  -- the same solution
            else solveMany s (insert (mn, n) Conflict us) eqs  -- conflicting solutions
        Nothing => solveMany s (insert (mn, n) (Unique tm) us) eqs  -- first solution
    Right moreEqs => solveMany s us (moreEqs ++ eqs)

covering export
solve : List Equality -> Either Solve.Error Subst
solve = solveMany empty empty
