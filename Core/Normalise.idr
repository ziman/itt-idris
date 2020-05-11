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
  matchPat : Globals q -> Subst q n pn -> Pat q pn -> TT q n -> Outcome (Subst q n pn)
  matchPat gs s (PV pv) tm = case s pv of
    Nothing => Match $ insert pv (Just tm) s
    Just _  => Error OvermatchedPatVar
  matchPat gs s (PForced _) _ = Match s
  matchPat gs s (PCtorApp ctor ps) tm =
    case unApply tm of
      (P cn, args) =>
        case .body <$> lookup cn gs of
          Just (Constructor arity) =>
            if ctorMatches ctor cn
              then case zipMatch (snd <$> ps) (snd <$> args) of
                Just psArgs =>
                  let psa = fromList psArgs
                    in matchPats gs s (fst <$> psa) (snd <$> psa)

                -- this happens when we're matching a forced constructor:
                -- wrong arity means this match is actually ill-typed
                -- which means that some other pattern must mismatch (we just haven't gotten there yet)
                -- because the clause is assumed to be forced-pattern-consistent
                -- so let's just conclude mismatch
                Nothing => Mismatch
              else Mismatch
          Just _ => Stuck  -- not a constructor
          Nothing => Error $ UnknownGlobal cn
      (V _, _) => Stuck
      _ => Mismatch
  matchPat gs s PWildcard _ = Match s

  matchPats : Globals q -> Subst q n pn -> Vect argn (Pat q pn) -> Vect argn (TT q n) -> Outcome (Subst q n pn)
  matchPats gs s [] [] = Match s
  matchPats gs s (p :: ps) (tm :: tms) =
    case matchPat gs s p tm of
      Match s' => matchPats gs s' ps tms
      Mismatch => Mismatch
      Error e  => Error e

      -- special case: if one pattern is stuck, some other pattern could still mismatch
      Stuck => case matchPats gs s ps tms of
        -- if we have a mismatch, the whole pattern mismatches
        Mismatch => Mismatch
        Error e => Error e

        -- otherwise we're stuck: we can't succeed here!
        _ => Stuck

matchClause : Globals q -> Clause q argn -> Vect argn (TT q n) -> Outcome (TT q n)
matchClause gs clause args =
  matchPats gs (\_ => Nothing) (snd <$> clause.lhs) args >>=
    \s => case fromSubst s of
      Nothing => Error UnmatchedPatVar
      Just vs => Match $ subst (\i => lookup i vs) clause.rhs

matchClauses : Globals q -> Vect argn (TT q n) -> List (Clause q argn) -> Outcome (TT q n)
matchClauses gs args [] = Mismatch
matchClauses gs args (c :: cs) =
  case matchClause gs c args of
    Match tm => Match tm
    Mismatch => matchClauses gs args cs
    Stuck => Stuck
    Error e => Error e

covering
mapArgs :
    (TT q n -> Either EvalError (TT q n))
    -> List (q, TT q n)
    -> Either EvalError (List (q, TT q n))
mapArgs nf = traverse (\(q', tm) => nf tm >>= \tmNF => Right (q', tmNF))

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
  red rf gs (App q f x) =
    red WHNF gs f >>= \case
      Lam b rhs => do
        xNF <- red operandForm gs x
        red rf gs $ subst (substFZ xNF) rhs
      fWHNF => case unApply' q fWHNF x of
        (P n, args) => case .body <$> lookup n gs of
          Nothing => Left $ UnknownGlobal n
          Just (Clauses argn cs) => case maybeTake argn args of
            Just (fargs, rest) => do
              fargsRed <- traverse (red operandForm gs . snd) fargs
              case matchClauses gs fargsRed cs of
                Match fx => red rf gs $ mkApp fx rest
                Mismatch => Left $ NoMatchingClause n
                Stuck => stuckTm rf gs (P n) args
                Error e => Left e
            Nothing => stuckTm rf gs (P n) args -- underapplied
          Just _ => stuckTm rf gs (P n) args -- not a pattern matching function
        (f, args) => stuckTm rf gs f args  -- not an application of a global
  red rf gs Type_ = pure Type_
  red rf gs Erased = pure Erased
  red rf gs (Meta i) = pure $ Meta i

  covering
  stuckTm : Form -> Globals q -> TT q n -> List (q, TT q n) -> Either EvalError (TT q n)
  stuckTm WHNF gs f args = pure $ mkApp f args
  stuckTm   NF gs f args = mkApp f <$> mapArgs (red NF gs) args
