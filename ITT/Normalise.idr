module ITT.Normalise

import public ITT.Core
import public ITT.Context
import public ITT.Module
import ITT.Lens
import Utils.Misc

%default total

export
substFZ : TT q n -> Fin (S n) -> TT q n
substFZ tm  FZ    = tm
substFZ tm (FS x) = V x

substScrut : Vect pn (TT q n) -> Fin (pn + n) -> TT q n
substScrut [] i = V i
substScrut (x :: _)   FZ    = x
substScrut (_ :: xs) (FS i) = substScrut xs i

lookup : Fin n -> Vect n a -> a
lookup FZ (x :: _) = x
lookup (FS i) (x :: xs) = lookup i xs

data MatchResult : (q : Type) -> (n : Nat) -> (pn : Nat) -> Type where
  Yes   : (ss : Vect pn (TT q n)) -> MatchResult q n pn
  No    : MatchResult q n pn
  Stuck : MatchResult q n pn

match : Globals q -> Vect k (TT q n)
    -> Name -> Telescope q (pn + n) s
    -> TT q n -> MatchResult q n (k + s)
match {k} glob ss cn [] (G n) with (Module.lookup n glob)
  | Just (D _ _ _ Constructor) =
      if n == cn
        then Yes (rewrite plusZeroRightNeutral k in ss)
        else No
  | _ = Stuck
match glob ss cn (b::bs) (App q f x) =
  replace (plusSuccRightSucc _ _)
    $ match glob (x::ss) cn bs f
match glob ss cn _ _ = Stuck  -- number of arguments doesn't match

mutual
  covering
  matchAlts : Globals q -> Context q n -> Vect pn (TT q n)
    -> TT q n -> List (Alt q n pn) -> Maybe (TT q n)
  matchAlts glob ctx ss scrut [] = Nothing  -- Stuck
  matchAlts glob ctx ss scrut (DefaultCase ct :: _) = 
    whnfCT glob ctx ss ct
  matchAlts glob ctx ss scrut (CtorCase cn args ct :: alts) =
    case match glob [] cn args scrut of
      Yes ss' => whnfCT glob ctx (ss' ++ ss) ct
      No      => matchAlts glob ctx ss scrut alts
      Stuck   => Nothing

  covering
  whnfCT : Globals q -> Context q n -> Vect pn (TT q n) -> CaseTree q n pn -> Maybe (TT q n)
  whnfCT glob ctx ss (Leaf rhs) = Just $ subst (substScrut ss) rhs
  whnfCT glob ctx ss (Case s alts) =
    matchAlts glob ctx ss (whnf glob ctx $ lookup s ss) alts
  whnfCT glob ctx ss (Forced s tm ct) =
    whnfCT glob ctx ss ct

  covering export
  whnf : Globals q -> Context q n -> TT q n -> TT q n
  whnf glob ctx (V i) = V i
  whnf glob ctx (G n) =
    case Module.lookup n glob of
      Just (D n q ty (Term tm)) => rename absurd $ whnf glob [] tm
      _ => G n
  whnf glob ctx (Lam b rhs) = Lam b rhs
  whnf glob ctx (Pi  b rhs) = Pi b rhs
  whnf glob ctx tm@(Let b val rhs)
    = whnf glob ctx $ subst (substFZ tm) rhs
  whnf glob ctx (App q f x) with (whnf glob ctx f)
    | Lam b rhs = whnf glob ctx $ subst (substFZ $ whnf glob ctx x) rhs
    | f' = App q f' x
  whnf glob ctx tm@(Match pvs ss ty ct) =
    case whnfCT glob ctx ss ct of
      Just result => result
      Nothing     => tm
  whnf glob ctx Star = Star
  whnf glob ctx Erased = Erased
