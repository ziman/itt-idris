module ITT.Normalise

import public ITT.Core
import public ITT.Context
import public ITT.Globals
import ITT.Lens
import Utils.Misc

%default total

export
substFZ : TT q n -> Fin (S n) -> TT q n
substFZ tm  FZ    = tm
substFZ tm (FS x) = V x

covering export
whnf : Globals q -> Context q n -> TT q n -> TT q n
whnf glob ctx (V i) = V i
whnf glob ctx (G n) =
  case Globals.lookup n glob of
    Just (D n q ty (Term tm)) => rename absurd tm
    _ => G n
whnf glob ctx (Lam b rhs) = Lam b rhs
whnf glob ctx (Pi  b rhs) = Pi b rhs
whnf glob ctx tm@(Let b val rhs)
  = whnf glob ctx $ subst (substFZ tm) rhs
whnf glob ctx (App q f x) with (whnf glob ctx f)
  | Lam b rhs = whnf glob ctx $ subst (substFZ $ whnf glob ctx x) rhs
  | f' = App q f' x
whnf glob ctx (Match ss pvs ct) = ?rhs
whnf glob ctx Star = Star
whnf glob ctx Erased = Erased
