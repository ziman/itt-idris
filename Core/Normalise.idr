module Core.Normalise

import public Core.TT
import public Core.Globals
import public Core.Context
import Core.TT.Lens
import Core.TT.Utils
import Utils.Misc

%default total
%undotted_record_projections off

data Error = UnknownGlobal Name

export
substFZ : TT q n -> Fin (S n) -> TT q n
substFZ tm  FZ    = tm
substFZ tm (FS x) = V x

substScrut : Vect pn (TT q n) -> Fin (pn + n) -> TT q n
substScrut [] i = V i
substScrut (x :: _)   FZ    = x
substScrut (_ :: xs) (FS i) = substScrut xs i

maybeTake : (n : Nat) -> List a -> Maybe (Vect n a, List a)
maybeTake Z xs = Just ([], xs)
maybeTake (S _) [] = Nothing
maybeTake (S n) (x :: xs) = maybeTake n xs <&> \case
  (ys, rest) => (x :: ys, rest)

data Outcome : a -> Type where
  Match : a -> Outcome a
  Mismatch : Outcome a
  Stuck : Outcome a

matchClauses : Vect argn (q, TT q n) -> List (Clause q argn) -> Maybe (TT q n)
matchClauses args cs = ?rhs_matchClauses

covering export
whnf : Globals q -> TT q n -> Either Error (TT q n)
whnf gs (P n) = pure $ P n
whnf gs (V i) = pure $ V i
whnf gs (Lam b rhs) = pure $ Lam b rhs
whnf gs (Pi  b rhs) = pure $ Pi b rhs
whnf gs (App q f x) =
  whnf gs f >>= \case
    Lam b rhs => do
      xWHNF <- whnf gs x
      whnf gs $ subst (substFZ xWHNF) rhs
    fWHNF => case unApply q fWHNF x of
      (P n, args) => case lookup n gs of
          Nothing => Left $ UnknownGlobal n
          Just (Clauses argn cs) => case maybeTake argn args of
              Just (fargs, rest) => case matchClauses fargs cs of
                  Just fx => whnf gs $ mkApp fx rest
                  Nothing => pure $ App q fWHNF x  -- stuck
              Nothing => pure $ App q fWHNF x  -- underapplied
          _ => pure $ App q fWHNF x  -- not a pattern matching function
whnf gs Type_ = pure Type_
whnf gs Erased = pure Erased
