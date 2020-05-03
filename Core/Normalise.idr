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
  | ConstructorArityMismatch PCtor Name
  | NoMatchingClause Name

export
Show EvalError where
  show (UnknownGlobal n) = "unknown global: " ++ show n
  show UnmatchedPatVar = "unmatched patvar"
  show OvermatchedPatVar = "overmatched patvar"
  show (ConstructorArityMismatch (Forced cn) n) = "constructor arity mismatch (forced): " ++ show (cn, n)
  show (ConstructorArityMismatch (Checked cn) n) = "constructor arity mismatch (checked): " ++ show (cn, n)
  show (NoMatchingClause n) = "no matching clause in " ++ show n

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

ctorMatches : PCtor -> Name -> Bool
ctorMatches (Forced _) _ = True
ctorMatches (Checked cn) cn' = cn == cn'

mutual
  matchPat : Subst q n pn -> Pat q pn -> TT q n -> Outcome (Subst q n pn)
  matchPat s (PV pv) tm = case s pv of
    Nothing => Match $ insert pv (Just tm) s
    Just _  => Error OvermatchedPatVar
  matchPat s (PForced _) _ = Match s
  matchPat s (PCtorApp ctor ps) tm =
    case unApply tm of
      (P cn, args) =>
        -- TODO: check that cn is actually a constructor
        -- if not, we should be stuck!
        if ctorMatches ctor cn
          then case zipMatch ps args of
            Just psArgs =>
              let psa = fromList psArgs
                in matchPats s (fst <$> psa) (snd <$> psa)

            -- this happens when we're matching a forced constructor:
            -- wrong arity means this match is actually ill-typed
            -- which means that some other pattern must mismatch (we just haven't gotten there yet)
            -- because the clause is assumed to be forced-pattern-consistent
            -- so let's just conclude mismatch
            Nothing => Mismatch
          else Mismatch
      (V _, _) => Stuck
      _ => Mismatch
  matchPat s PWildcard _ = Match s

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

matchClauses : Vect argn (TT q n) -> List (Clause q argn) -> Outcome (TT q n)
matchClauses args [] = Mismatch
matchClauses args (c :: cs) =
  case matchClause c args of
    Match tm => Match tm
    Mismatch => matchClauses args cs
    Stuck => Stuck
    Error e => Error e

public export
data Form = NF | WHNF

operandForm : Form
operandForm = NF

mutual
  covering export
  red : Form -> Globals q -> TT q n -> Either EvalError (TT q n)
  red rf gs (P n) =
    case .body <$> lookup n gs of
      -- constant pattern matching functions
      Just (Clauses Z [MkClause [] [] rhs]) =>
        red rf gs $ weakenClosed rhs
      _ => pure $ P n
  red rf gs (V i) = pure $ V i
  red WHNF gs (Lam b rhs) = pure $ Lam b rhs
  red   NF gs (Lam (B n q ty) rhs) = do
    tyNF <- red NF gs ty
    Lam (B n q tyNF) <$> red NF gs rhs
  red WHNF gs (Pi b rhs) = pure $ Pi b rhs
  red   NF gs (Pi (B n q ty) rhs) = do
    tyNF <- red NF gs ty
    Pi (B n q tyNF) <$> red NF gs rhs
  red rf gs (App f x) =
    red WHNF gs f >>= \case
      Lam b rhs => do
        xNF <- red operandForm gs x
        red rf gs $ subst (substFZ xNF) rhs
      fWHNF => case unApply' fWHNF x of
        (P n, args) => case .body <$> lookup n gs of
          Nothing => Left $ UnknownGlobal n
          Just (Clauses argn cs) => case maybeTake argn args of
            Just (fargs, rest) => do
              fargsRed <- traverse (red operandForm gs) fargs
              case matchClauses fargsRed cs of
                Match fx => red rf gs $ mkApp fx rest
                Mismatch => Left $ NoMatchingClause n
                Stuck => stuckTm rf gs n args
                Error e => Left e
            Nothing => stuckTm rf gs n args -- underapplied
          _ => stuckTm rf gs n args -- not a pattern matching function
  red rf gs Type_ = pure Type_
  red rf gs Erased = pure Erased

  covering
  stuckTm : Form -> Globals q -> Name -> List (TT q n) -> Either EvalError (TT q n)
  stuckTm WHNF gs n args = pure $ mkApp (P n) args
  stuckTm   NF gs n args = mkApp (P n) <$> traverse (red NF gs) args
