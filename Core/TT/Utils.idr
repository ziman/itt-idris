module Core.TT.Utils

import public Core.TT

%default total
%undotted_record_projections off

export
unApply' : q -> TT q n -> TT q n -> (TT q n, List (q, TT q n))
unApply' q_ f x = go f [(q_,x)]
  where
    go : TT q n -> List (q, TT q n) -> (TT q n, List (q, TT q n))
    go (App q f x) args = go f ((q,x) :: args)
    go f args = (f, args)

export
unApply : TT q n -> (TT q n, List (q, TT q n))
unApply (App q f x) = unApply' q f x
unApply tm = (tm, [])

export
mkApp : TT q n -> List (q, TT q n) -> TT q n
mkApp f [] = f
mkApp f ((q, x) :: xs) = mkApp (App q f x) xs
