module Utils

import public Data.Fin

export
finEq : Fin n -> Fin n -> Bool
finEq FZ FZ = True
finEq FZ (FS _) = False
finEq (FS _) FZ = False
finEq (FS x) (FS y) = finEq x y

export
eqBy : Eq b => (a -> b) -> a -> a -> Bool
eqBy f x y = f x == f y

export
compareBy : Ord b => (a -> b) -> a -> a -> Ordering
compareBy f x y = compare (f x) (f y)

public export
record Or where
  constructor MkOr
  runOr : Bool

public export
Semigroup Or where
  (<+>) (MkOr False) (MkOr False) = MkOr False
  (<+>) _ _ = MkOr True

public export
Monoid Or where
  neutral = MkOr False
