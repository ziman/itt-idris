module Core.TT.Utils

import public Core.TT
import public Data.SortedSet
import Data.List

%default total

export
unApply' : q -> TT q n -> TT q n -> (TT q n, List (q, TT q n))
unApply' qv f x = go f [(qv, x)]
  where
    go : TT q n -> List (q, TT q n) -> (TT q n, List (q, TT q n))
    go (App q f x) args = go f ((q, x) :: args)
    go f args = (f, args)

export
unApply : TT q n -> (TT q n, List (q, TT q n))
unApply (App q f x) = unApply' q f x
unApply tm = (tm, [])

export
mkApp : TT q n -> List (q, TT q n) -> TT q n
mkApp f = foldl (\g, (q, x) => App q g x) f

export
piDepth : TT q n -> Nat
piDepth (Pi b rhs) = S (piDepth rhs)
piDepth _ = Z

export
hasTypeTarget : TT q n -> Bool
hasTypeTarget (Pi b rhs) = hasTypeTarget rhs
hasTypeTarget Type_ = True
hasTypeTarget _ = False

-- returns (covariant, contravariant)
export
getVariance : Ord q => TT q n -> (SortedSet q, SortedSet q)
getVariance (Pi (B n q ty) rhs) =
  case (getVariance ty, getVariance rhs) of
    ((coTy, contraTy), (coRhs, contraRhs)) =>
      (coRhs <+> contraTy, insert q contraRhs <+> coTy)
getVariance _ = (empty, empty)
