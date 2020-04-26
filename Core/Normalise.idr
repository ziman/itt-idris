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

Subst : Type -> Nat -> Nat -> Type
Subst q n pn = Fin pn -> Maybe (TT q n)

fromSubst : {n : Nat} -> (Fin n -> Maybe a) -> Maybe (Vect n a)
fromSubst {n = Z}   g = pure []
fromSubst {n = S n} g = [| g FZ :: fromSubst (g . FS) |]

matchPat : Subst q n pn -> Pat q pn -> TT q n -> Outcome (Subst q n pn)
matchPat s pat tm = ?rhs1

matchPats : Subst q n pn -> Vect argn (Pat q pn) -> Vect argn (q, TT q n) -> Outcome (Subst q n pn)
matchPats s [] [] = Match s
matchPats s (p :: ps) ((_, tm) :: tms) =
  case matchPat s p tm of
    Match s' => matchPats s' ps tms
    Mismatch => Mismatch
    Stuck => Stuck

matchClause : Clause q argn -> Vect argn (q, TT q n) -> Outcome (TT q n)
matchClause clause args =
  case matchPats (\_ => Nothing) clause.lhs args of
    Match s => case fromSubst s of
      Nothing => Stuck  -- something's wrong with the patterns
      Just vs => Match $ subst (\i => lookup i vs) clause.rhs
    Mismatch => Mismatch
    Stuck => Stuck

matchClauses : Vect argn (q, TT q n) -> List (Clause q argn) -> Maybe (TT q n)
matchClauses args [] = Nothing
matchClauses args (c :: cs) =
  case matchClause c args of
    Match tm => Just tm
    Mismatch => matchClauses args cs
    Stuck => Nothing

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
