module ITT.Normalise

import public ITT.Core
import public ITT.Context
import ITT.Lens

%default total

export
substFZ : TT q n -> Fin (S n) -> TT q n
substFZ tm  FZ    = tm
substFZ tm (FS x) = V x

mapFZ : Fin n -> Fin (S n) -> Fin n
mapFZ i  FZ    = i
mapFZ _ (FS j) = j

Strengthen (TT q) where
  strengthen = ttVars (map V . strengthen)

covering export
whnf : Context q n -> TT q n -> TT q n
whnf ctx (V i) with (lookupCtx i ctx)
  | D n r ty (Term tm) = whnf ctx $ strengthen tm
  | _ = V i
whnf ctx (Lam d rhs) = ?rlam
whnf ctx (Pi d rhs) = ?rlam
whnf ctx (Let d val rhs) = ?rlam
whnf ctx (App q f x) with (whnf ctx f)
  | Bind Lam d rhs = whnf ctx $ subst (substFZ $ whnf ctx x) rhs
  | f' = App q f' x
whnf ctx Star = Star
whnf ctx Erased = Erased
