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
  matchAlts : Globals q -> Vect pn (TT q n)
    -> TT q n -> List (Alt q n pn) -> Maybe (TT q n)
  matchAlts glob ss scrut [] = Nothing  -- Stuck
  matchAlts glob ss scrut (DefaultCase ct :: _) = 
    whnfCT glob ss ct
  matchAlts glob ss scrut (CtorCase cn args ct :: alts) =
    case match glob [] cn args scrut of
      Yes ss' => whnfCT glob (ss' ++ ss) ct
      No      => matchAlts glob ss scrut alts
      Stuck   => Nothing

  covering
  whnfCT : Globals q -> Vect pn (TT q n) -> CaseTree q n pn -> Maybe (TT q n)
  whnfCT glob ss (Leaf rhs) = Just $ subst (substScrut ss) rhs
  whnfCT glob ss (Case s alts) =
    matchAlts glob ss (whnf glob $ lookup s ss) alts
  whnfCT glob ss (Forced s tm ct) =
    whnfCT glob ss ct

  covering export
  whnf : Globals q -> TT q n -> TT q n
  whnf glob (V i) = V i
  whnf glob (G n) =
    case Module.lookup n glob of
      Just (D n q ty (Term tm)) => rename absurd $ whnf glob tm
      _ => G n
  whnf glob (Lam b rhs) = Lam b rhs
  whnf glob (Pi  b rhs) = Pi b rhs
  whnf glob tm@(Let b val rhs)
    = whnf glob $ subst (substFZ tm) rhs
  whnf glob (App q f x) with (whnf glob f)
    | Lam b rhs = whnf glob $ subst (substFZ $ whnf glob x) rhs
    | f' = App q f' x
  whnf glob tm@(Match pvs ss ty ct) =
    case whnfCT glob ss ct of
      Just result => result
      Nothing     => tm
  whnf glob Star = Star
  whnf glob Erased = Erased
