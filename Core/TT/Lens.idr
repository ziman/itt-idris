module Core.TT.Lens

import Utils.Misc
import public Core.TT
import Control.Monad.Identity

%default total

public export
Traversal : Type -> Type -> Type -> Type -> Type
Traversal s t a b = (
    {0 f : Type -> Type} -> Applicative f => (a -> f b) -> s -> f t
  )

public export
Lens : Type -> Type -> Type
Lens t a = Traversal t t a a

public export
ILens : (a -> Type) -> (a -> Type) -> Type
ILens {a} f g = {x, y : a} -> Traversal (f x) (f y) (g x) (g y)

mutual
  export
  bindingQ : Traversal (Binding q n) (Binding q' n) q q'
  bindingQ g (B n q ty) = B n <$> g q <*> ttQ g ty

  export
  ttQ : Traversal (TT q n) (TT q' n) q q'
  ttQ g (P n) = pure $ P n
  ttQ g (V i) = pure $ V i
  ttQ g (Lam b rhs) = Lam <$> bindingQ g b <*> ttQ g rhs
  ttQ g (Pi  b rhs) = Pi  <$> bindingQ g b <*> ttQ g rhs
  ttQ g (App q f x) = App <$> g q <*> ttQ g f <*> ttQ g x
  ttQ g Type_ = pure Type_
  ttQ g Erased = pure Erased
  ttQ g (Meta i) = pure $ Meta i

mutual
  export
  skipFZ : Applicative t => (Fin n -> t (TT q m)) -> Fin (S n) -> t (TT q (S m))
  skipFZ g  FZ    = pure (V FZ)
  skipFZ g (FS i) = rename FS <$> g i

  export
  bindingVars : Traversal (Binding q m) (Binding q n) (Fin m) (TT q n)
  bindingVars g (B n q ty) = B n q <$> ttVars g ty

  export
  ttVars : Traversal (TT q m) (TT q n) (Fin m) (TT q n)
  ttVars g (P n) = pure $ P n
  ttVars g (V i) = g i
  ttVars g (Lam b rhs) = Lam <$> bindingVars g b <*> ttVars (skipFZ g) rhs
  ttVars g (Pi  b rhs) = Pi  <$> bindingVars g b <*> ttVars (skipFZ g) rhs
  ttVars g (App q f x) = App q <$> ttVars g f <*> ttVars g x
  ttVars g Type_ = pure Type_
  ttVars g Erased = pure Erased
  ttVars g (Meta i) = pure $ Meta i

  export
  subst : (Fin n -> TT q m) -> TT q n -> TT q m
  subst g = assert_total $ runIdentity . ttVars (pure . g)

  export
  rename : (Fin n -> Fin m) -> TT q n -> TT q m
  rename g = subst (V . g)

export
fold : Monoid a => (Fin n -> a) -> TT q n -> a
fold {n} f = runConst . ttVars {n} (MkConst . f)

-- repeated weakening, identity at runtime
export
tackFinL : Fin s -> Fin (s + n)
tackFinL  FZ    = FZ
tackFinL (FS i) = FS $ tackFinL i

export
weakenClosed : TT q Z -> TT q n
weakenClosed = rename tackFinL

export
weakenClosedBinding : Binding q Z -> Binding q n
weakenClosedBinding (B n q ty) = B n q (weakenClosed ty)

export
mapQ : Traversal a b q q' -> (q -> q') -> a -> b
mapQ f g = runIdentity . f (pure . g)

export
eraseQ : Traversal a b q () -> a -> b
eraseQ f = mapQ f (const ())

fromNat : (n : Nat) -> Fin (S k + n)
fromNat    Z  = FZ
fromNat (S n) = FS $ replace {p = Fin} (plusSuccRightSucc k n) (fromNat n)

plusFin : Fin n -> (d : Nat) -> Fin (n + d)
plusFin    FZ  d = fromNat d
plusFin (FS i) d = FS $ plusFin i d

minusFin : (d : Nat) -> (n : Nat) -> Fin (n + d) -> Maybe (Fin n)
minusFin    Z  n i = Just $ replace {p = Fin} (plusZeroRightNeutral n) i
minusFin (S d) n i with (replace {p = Fin} (sym $ plusSuccRightSucc n d) i)
  minusFin (S d) n i |    FZ = Nothing  -- can't subtract (S d) from FZ
  minusFin (S d) n i | FS i' = minusFin d n i'

rescopeFin : (m : Nat) -> (n : Nat) -> Fin m -> Maybe (Fin n)
rescopeFin m n i with (cmp m n)
  rescopeFin m (m + S d) i | CmpLT d = Just $ i `plusFin` S d
  rescopeFin n         n i | CmpEQ   = Just i
  rescopeFin (n + S d) n i | CmpGT d = minusFin (S d) n i

export
rescope : {m : Nat} -> {n : Nat} -> Traversal a b (Fin m) (TT q n) -> a -> Maybe b
rescope trav = trav (map V . rescopeFin m n)
