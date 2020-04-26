module Core.Normalise

import public Core.TT
import public Core.Globals
import public Core.Context
import Core.TT.Lens
import Core.TT.Utils
import Utils.Misc

%default total
%undotted_record_projections off

public export
data EvalError
  = UnknownGlobal Name
  | UnmatchedPatVar
  | OvermatchedPatVar
  | ConstructorArityMismatch

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

data Outcome : Type -> Type where
  Match : a -> Outcome a
  Mismatch : Outcome a
  Stuck : Outcome a
  Error : EvalError -> Outcome a

Functor Outcome where
  map f (Match a) = Match (f a)
  map f Mismatch = Mismatch
  map f Stuck = Stuck
  map f (Error e) = Error e

Applicative Outcome where
  pure = Match
  Match f <*> x = f <$> x
  Mismatch <*> _ = Mismatch
  Stuck <*> _ = Stuck
  Error e <*> _ = Error e

Monad Outcome where
  Match x >>= f = f x
  Mismatch >>= f = Mismatch
  Stuck >>= f = Stuck
  Error e >>= f = Error e

Subst : Type -> Nat -> Nat -> Type
Subst q n pn = Fin pn -> Maybe (TT q n)

fromSubst : {n : Nat} -> (Fin n -> Maybe a) -> Maybe (Vect n a)
fromSubst {n = Z}   g = pure []
fromSubst {n = S n} g = [| g FZ :: fromSubst (g . FS) |]

insert : Eq k => k -> v -> (k -> v) -> (k -> v)
insert k v f x =
  if x == k
    then v
    else f x

zipMatch : List a -> List b -> Maybe (List (a, b))
zipMatch [] [] = Just []
zipMatch (x :: xs) (y :: ys) = ((x,y) ::) <$> zipMatch xs ys
zipMatch _ _ = Nothing

mutual
  matchPat : Subst q n pn -> Pat q pn -> TT q n -> Outcome (Subst q n pn)
  matchPat s (PV pv) tm = case s pv of
    Nothing => Match $ insert pv (Just tm) s
    Just _  => Error OvermatchedPatVar
  matchPat s (PForced _) _ = Match s
  matchPat s (PCtor isForced cn ps) tm =
    case unApply tm of
      (P cn', args) =>
          if cn' == cn
            then case zipMatch (snd <$> ps) (snd <$> args) of
              Just psArgs =>
                let psa = fromList psArgs
                  in matchPats s (fst <$> psa) (snd <$> psa)
              Nothing => Error ConstructorArityMismatch
            else Mismatch
      (V _, _) => Stuck
      _ => Mismatch

  matchPats : Subst q n pn -> Vect argn (Pat q pn) -> Vect argn (TT q n) -> Outcome (Subst q n pn)
  matchPats s [] [] = Match s
  matchPats s (p :: ps) (tm :: tms) =
    matchPat s p tm >>=
      \s' => matchPats s' ps tms

matchClause : Clause q argn -> Vect argn (TT q n) -> Outcome (TT q n)
matchClause clause args =
  matchPats (\_ => Nothing) clause.lhs args >>=
    \s => case fromSubst s of
      Nothing => Error UnmatchedPatVar
      Just vs => Match $ subst (\i => lookup i vs) clause.rhs

matchClauses : Vect argn (TT q n) -> List (Clause q argn) -> Maybe (TT q n)
matchClauses args [] = Nothing
matchClauses args (c :: cs) =
  case matchClause c args of
    Match tm => Just tm
    Mismatch => matchClauses args cs
    Stuck => Nothing

covering export
whnf : Globals q -> TT q n -> Either EvalError (TT q n)
whnf gs (P n) = pure $ P n
whnf gs (V i) = pure $ V i
whnf gs (Lam b rhs) = pure $ Lam b rhs
whnf gs (Pi  b rhs) = pure $ Pi b rhs
whnf gs (App q f x) =
  whnf gs f >>= \case
    Lam b rhs => do
      xWHNF <- whnf gs x
      whnf gs $ subst (substFZ xWHNF) rhs
    fWHNF => case unApply' q fWHNF x of
      (P n, args) => case lookup n gs of
          Nothing => Left $ UnknownGlobal n
          Just (Clauses argn cs) => case maybeTake argn args of
              Just (fargs, rest) => case matchClauses (snd <$> fargs) cs of
                  Just fx => whnf gs $ mkApp fx rest
                  Nothing => pure $ App q fWHNF x  -- stuck
              Nothing => pure $ App q fWHNF x  -- underapplied
          _ => pure $ App q fWHNF x  -- not a pattern matching function
whnf gs Type_ = pure Type_
whnf gs Erased = pure Erased
