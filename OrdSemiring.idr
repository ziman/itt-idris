module OrdSemiring

import Data.Vect

%default total

infixl 4 .+.
infixl 5 .*.
infix  3 .<=.
public export
interface OrdSemiring a where
  semi0 : a
  semi1 : a
  (.+.) : a -> a -> a
  (.*.) : a -> a -> a
  (.<=.) : a -> a -> Bool

infixl 4 <.+.>
export
(<.+.>) : OrdSemiring a => Vect n a -> Vect n a -> Vect n a
(<.+.>) = zipWith (.+.)

infixl 5 <.*.>
export
(<.*.>) : OrdSemiring a => Vect n a -> Vect n a -> Vect n a
(<.*.>) = zipWith (.*.) 

infixl 3 <.<=.>
export
(<.<=.>) : OrdSemiring a => Vect n a -> Vect n a -> Vect n Bool
(<.<=.>) = zipWith (.<=.)
