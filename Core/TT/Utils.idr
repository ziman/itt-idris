module Core.TT.Utils

import public Core.TT
import Data.List

%default total
%undotted_record_projections off

export
unApply' : TT q n -> TT q n -> (TT q n, List (TT q n))
unApply' f x = go f [x]
  where
    go : TT q n -> List (TT q n) -> (TT q n, List (TT q n))
    go (App f x) args = go f (x :: args)
    go f args = (f, args)

export
unApply : TT q n -> (TT q n, List (TT q n))
unApply (App f x) = unApply' f x
unApply tm = (tm, [])

export
mkApp : TT q n -> List (TT q n) -> TT q n
mkApp f = foldl App f

export
hasTypeTarget : TT q n -> Bool
hasTypeTarget (Pi b rhs) = hasTypeTarget rhs
hasTypeTarget Type_ = True
hasTypeTarget _ = False
