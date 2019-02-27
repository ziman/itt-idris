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

insertEq : (p, q : Evar) -> EqGraph -> Either ErrMsg EqGraph

-- quantity ~ quantity
insertEq (QQ q) (QQ q') eg with (q == q')
  | True  = Right eg
  | False = Left $ MismatchedQ q q'

-- evar ~ quantity
insertEq (QQ q) (EV i) eg = insertEq (EV i) (QQ q) eg
insertEq (EV i) (QQ q) eg@(EG cls idx) =
  case Map.lookup i idx of
    -- evar not seen yet
    Nothing => Right $ EG cls (Map.insert i (Solved q) idx)

    -- evar already solved -> check if consistent
    Just (Solved q') => if q == q'
      then Right eg  -- nothing to do
      else Left $ MismatchedQ q q'

    -- evar present in an equivalence class
    -- eliminate the whole class and mark it as solved
    Just (RepresentedBy r) => case Map.lookup r cls of
      Nothing => Left $ Impossible "eqclass not found"
      Just ns => Right $ EG
        (Map.delete r cls)
        (foldr (\v => Map.insert v (Solved q)) idx $ Set.toList ns)

-- evar ~ evar
insertEq (EV i) (EV j) (EG cls idx)
  with (Map.lookup i idx, Map.lookup j idx)
  -- neither variable exists: create a new equivalence class
  | (Nothing, Nothing) = Right $ EG
      (Map.insert i (Set.fromList [i, j]) $ cls)
      (Map.insert i (RepresentedBy i) . Map.insert j (RepresentedBy i) $ idx)

  | (x, y) = ?rhs

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
