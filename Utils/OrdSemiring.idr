module Utils.OrdSemiring

import Data.Vect

%default total

export infixl 5 .+.
export infixl 6 .*.
export infix  3 .<=.
export infix  4 .\/.
public export
interface OrdSemiring a where
  semi0 : a
  semi1 : a
  top : a
  (.+.) : a -> a -> a
  (.*.) : a -> a -> a
  (.\/.) : a -> a -> a
  (.<=.) : a -> a -> Bool
