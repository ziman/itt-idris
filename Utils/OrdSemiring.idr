module Utils.OrdSemiring

import Data.Vect

%default total

infixl 5 .+.
infixl 6 .*.
infix  3 .<=.
infix  4 .\/.
public export
interface OrdSemiring a where
  semi0 : a
  semi1 : a
  top : a
  (.+.) : a -> a -> a
  (.*.) : a -> a -> a
  (.\/.) : a -> a -> a
  (.<=.) : a -> a -> Bool
