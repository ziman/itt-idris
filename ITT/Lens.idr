module ITT.Lens

import public ITT.Core
import Control.Monad.Identity

public export
Traversal : Type -> Type -> Type -> Type -> Type
Traversal s t a b = (
  {f : Type -> Type} -> Applicative f => (a -> f b) -> s -> f t
)

public export
Lens : Type -> Type -> Type
Lens t a = Traversal t t a a

public export
ILens : (a -> Type) -> (a -> Type) -> Type
ILens {a} f g = {x, y : a} -> Traversal (f x) (f y) (g x) (g y)

mutual
  bodyQ : Traversal (Body q n) (Body q' n) q q'
  bodyQ g (Abstract a) = pure $ Abstract a
  bodyQ g (Term tm) = Term <$> ttQ g tm

  export
  ttQ : Traversal (TT q n) (TT q' n) q q'
  ttQ g (V i) = pure $ V i
  ttQ g (Bind b (D n q ty db) rhs)
    = Bind b <$> (D n <$> g q <*> ttQ g ty <*> bodyQ g db) <*> ttQ g rhs
  ttQ g (App q f x) = App <$> g q <*> ttQ g f <*> ttQ g x
  ttQ g Star = pure Star
  ttQ g Erased = pure Erased

mutual
  nonFZS : Applicative t => (Fin n -> t (TT q m)) -> Fin (S n) -> t (TT q (S m))
  nonFZS g  FZ    = pure (V FZ)
  nonFZS g (FS i) = assert_total (runIdentity . ttVars (pure . V . FS) <$> g i)

  bodyVars : Traversal (Body q m) (Body q n) (Fin m) (TT q n)
  bodyVars g (Abstract a) = pure $ Abstract a
  bodyVars g (Term tm) = Term <$> ttVars g tm

  defVars : Traversal (Def q m) (Def q n) (Fin m) (TT q n)
  defVars g (D n q ty b) = D n q <$> ttVars g ty <*> bodyVars (nonFZS g) b

  export
  ttVars : Traversal (TT q m) (TT q n) (Fin m) (TT q n)
  ttVars g (V i) = g i
  ttVars g (Bind b d rhs)
    = Bind b <$> defVars g d <*> ttVars (nonFZS g) rhs
  ttVars g (App q f x)
    = App q <$> ttVars g f <*> ttVars g x
  ttVars g Star = pure Star
  ttVars g Erased = pure Erased

export
fold : Monoid a => (Fin n -> a) -> TT q n -> a
fold {n} f = runConst . ttVars {n} (MkConst . f)

export
subst : (Fin n -> TT q m) -> TT q n -> TT q m
subst g = runIdentity . ttVars (pure . g)

export
rename : (Fin n -> Fin m) -> TT q n -> TT q m
rename g = subst (V . g)
