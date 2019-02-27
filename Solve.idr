module Solve

import public TT
import public Infer
import public Data.SortedMap as Map
import Data.SortedSet as Set

%default total

Map : Type -> Type -> Type
Map = SortedMap

public export
data ErrMsg : Type where
  MismatchedQ : (p, q : Q) -> ErrMsg
  Impossible : String -> ErrMsg

public export
Solution : Type
Solution = SortedMap ENum Q

data Grouping
  = Solved Q
  | RepresentedBy ENum

record EqGraph where
  constructor EG

  -- representant -> equivalence class
  classes : Map ENum (Set ENum)

  -- element -> representant/solution
  index : Map ENum Grouping

setSingle : Ord a => a -> Set a
setSingle x = Set.insert x Set.empty

setSize : Set a -> Nat
setSize = length . Set.toList

insertWith : Semigroup v => (v -> v -> v) -> k -> v -> Map k v -> Map k v
insertWith (+) k v m with (Map.lookup k m)
  | Just v' = Map.insert k (v <+> v') m
  | Nothing = Map.insert k v m

insertQEqQ : (p, q : Q) -> EqGraph -> Either ErrMsg EqGraph
insertQEqQ p q eg =
  if p == q
    then Right eg
    else Left $ MismatchedQ p q

newClass : (r : ENum) -> List ENum -> EqGraph -> Either ErrMsg EqGraph
newClass r vs (EG cls idx) = Right $ EG
  (Map.insert r (Set.fromList (r :: vs)) cls)
  (foldr (\v => Map.insert v (RepresentedBy r)) idx $ r :: vs)

growClass : (r : ENum) -> List ENum -> EqGraph -> Either ErrMsg EqGraph
growClass r newVs (EG cls idx) =
  case Map.lookup r cls of
    Nothing => Left $ Impossible "growClass"
    Just vs => Right $ EG
      (Map.insert r (foldr Set.insert vs newVs) cls)
      (foldr (\v => Map.insert v (RepresentedBy r)) idx newVs)

mapClass : (r : ENum) -> Grouping -> EqGraph -> Either ErrMsg EqGraph
mapClass oldR g (EG cls idx) =
  case Map.lookup oldR cls of
    Nothing => Left $ Impossible "mapClass"
    Just vs => Right $ EG
      (case g of
        -- just delete the equivalence class
        Solved _ => Map.delete oldR cls
        -- move the equivalence class under a different representant
        RepresentedBy newR => insertWith Set.union newR vs . Map.delete oldR $ cls
      )
      (foldr (\v => Map.insert v g) idx $ Set.toList vs)

insertEvarEqQ : (i : ENum) -> (q : Q) -> EqGraph -> Either ErrMsg EqGraph
insertEvarEqQ i q eg@(EG cls idx) =
  case Map.lookup i idx of
    -- evar not seen yet, just mark as solved
    Nothing => Right $ EG cls (Map.insert i (Solved q) idx)

    -- evar already solved -> check if consistent
    Just (Solved q') => insertQEqQ q q' eg

    -- evar present in an equivalence class
    -- eliminate the whole class and mark it as solved
    Just (RepresentedBy r) => mapClass r (Solved q) eg

insertEvarEqEvar : (i, j : ENum) -> EqGraph -> Either ErrMsg EqGraph
insertEvarEqEvar i j eg@(EG cls idx) = case (Map.lookup i idx, Map.lookup j idx) of
  (Nothing, Nothing) => newClass i [i,j] eg
  (Just (Solved q), Nothing) => insertEvarEqQ j q eg
  (Nothing, Just (Solved q)) => insertEvarEqQ i q eg
  (Just (RepresentedBy r), Just g) => mapClass r g eg
  (Just g, Just (RepresentedBy r)) => mapClass r g eg
  (Just (RepresentedBy r), Nothing) => growClass r [j] eg
  (Nothing, Just (RepresentedBy r)) => growClass r [i] eg

insertEq : (p, q : Evar) -> EqGraph -> Either ErrMsg EqGraph
insertEq (QQ q) (QQ q') eg = insertQEqQ q q' eg
insertEq (QQ q) (EV i) eg = insertEvarEqQ i q eg
insertEq (EV i) (QQ q) eg = insertEvarEqQ i q eg
insertEq (EV i) (EV j) eg = insertEvarEqEvar i j eg

getEqGraph : List Constr -> Either ErrMsg EqGraph
getEqGraph = foldlM f (EG Map.empty Map.empty)
  where
    f : EqGraph -> Constr -> Either ErrMsg EqGraph
    f eg (CEq v w) = insertEq v w eg
    f eg _ = Right eg

{-
getUsages : List Constr -> Map Evar (List (Set Evar))
getUsages [] = Map.empty
getUsages (CLeq gs q :: cs)
    = insertWith (++) q [gs] $ getUsages cs
getUsages (_ :: cs) = getUsages cs

export
solve : List Constr -> Either ErrMsg Solution
solve c = ?rhs2
-}
