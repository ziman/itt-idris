module ITT.Normalise

import public ITT.Core
import ITT.Lens

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
  | D n q ty (Abstract _) = V i
  -- replace recursive references by reference #i
  | D n q ty (Term body)  = whnf ctx $ rename (mapFZ i) body
whnf ctx (Bind Let d rhs) =
  let rhs' = whnf (d::ctx) rhs
    in case ttVars (map V . unFS) rhs' of
      Just rhs'' => rhs''
      Nothing    => Bind Let d rhs'
whnf ctx (Bind b d rhs) = Bind b d rhs
whnf ctx (App q f x) with (whnf ctx f)
  | Bind Lam d rhs = whnf ctx $ subst (substFZ $ whnf ctx x) rhs
  | f' = App q f' x
whnf ctx Star = Star
whnf ctx Erased = Erased
