module Utils.Misc

import public Data.Fin
import public Data.Vect

%default total

infixl 3 <&>
%inline
public export
(<&>) : Functor f => f a -> (a -> b) -> f b
(<&>) x f = f <$> x

infixl 2 =<<
%inline
public export
(=<<) : Monad m => (a -> m b) -> m a -> m b
(=<<) f x = x >>= f

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

export
lookup : Fin n -> Vect n a -> a
lookup  FZ    (x :: _) = x
lookup (FS i) (x :: xs) = lookup i xs

export
Semigroup Or where
  (<+>) (MkOr False) (MkOr False) = MkOr False
  (<+>) _ _ = MkOr True

export
Monoid Or where
  neutral = MkOr False

public export
record Const (a : Type) (b : Type) where
  constructor MkConst
  value : a

export
runConst : Const a b -> a
runConst c = c.value

export
Functor (Const a) where
  map f (MkConst x) = MkConst x

export
Monoid a => Applicative (Const a) where
  pure _ = MkConst neutral
  (<*>) (MkConst x) (MkConst y) = MkConst (x <+> y)

export
unFS : Fin (S n) -> Maybe (Fin n)
unFS  FZ    = Nothing
unFS (FS i) = Just i
