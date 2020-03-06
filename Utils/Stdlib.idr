module Utils.Stdlib

import Data.List

%default total

export
transpose : List (List a) -> List (List a)
transpose [] = []
transpose [row] = map (:: []) row
transpose (row :: rows) = zipWith (::) row (transpose rows)
