module Utils.OrdSemiring

import Data.Vect

%default total

infixl 4 .+.
infixl 5 .*.
infix  3 .<=.
public export
interface OrdSemiring a where
  semi0 : a
  semi1 : a
  top : a
  (.+.) : a -> a -> a
  (.*.) : a -> a -> a
  (.\/.) : a -> a -> a
  (.<=.) : a -> a -> Bool
