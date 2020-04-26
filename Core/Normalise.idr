module ITT.Normalise

import public ITT.Core
import public ITT.Context
import ITT.Core.Lens
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

mutual
  covering export
  whnf : TT q n -> TT q n
  whnf (V i) = V i
  whnf (Lam b rhs) = Lam b rhs
  whnf (Pi  b rhs) = Pi b rhs
  whnf (App q f x) = case whnf f of
    Lam b rhs => whnf $ subst (substFZ $ whnf x) rhs
    f' => App q f' x
  whnf Star = Star
  whnf Erased = Erased

  whnf Bool_ = Bool_
  whnf (If_ c t e) = case whnf c of
    True_  => whnf t
    False_ => whnf e
    c' => If_ c' t e
  whnf True_ = True_
  whnf False_ = False_
