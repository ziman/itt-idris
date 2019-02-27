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

public export
Solution : Type
Solution = SortedMap ENum Q

record EqGraph where
  constructor EG

  -- representant -> equivalence class
  classes : Map ENum (Set ENum)

  -- element -> representant
  index : Map ENum ENum

  -- concrete assignments we can already give
  concrete : Map ENum Q

setSingle : Ord a => a -> Set a
setSingle x = Set.insert x Set.empty

setSize : Set a -> Nat
setSize = length . Set.toList

insertEq : (p, q : Evar) -> EqGraph -> Either ErrMsg EqGraph

-- two hard quantities
insertEq (QQ q) (QQ q') g with (q == q')
  | True  = pure g
  | False = Left $ MismatchedQ q q'

-- hard assignment for an evar
insertEq (QQ q) (EV i) g = insertEq (EV i) (QQ q) g
insertEq (EV i) (QQ q) (EG cls idx sol) =
  case Map.lookup i idx of
    -- evar not seen yet
    Nothing => EG cls idx $ Map.insert i p sol

    -- evar present in an equivalence class
    -- eliminate the whole class and mark it as solved
    Just r => case Map.lookup r cls of
      Nothing => assert_unreachable
      Just ns => EG
        (M.delete r cls)
        (foldr Map.delete idx $ Set.toList ns)
        (foldr (\i -> Map.insert i q) sol $ Set.toList ns)

insertEq (EV i) (EV j) (EG cls idx sol)
  with (M.lookup i idx, M.lookup j idx)
  | (Nothing, Nothing) = EG
      (M.insert i (setSingle i) . M.insert j (setSingle j) $ cls)
      (M.insert i i . M.insert j j $ cls)
      sol
  | (Nothing, Just jr) = EG
      (M.insertWith S.union jr (setSingle i) cls)
      (M.insert i jr idx)
      sol
  | (Just ir, Nothing) = EG
      (M.insertWith S.union ir (setSingle j) cls)
      (M.insert j ir idx)
      sol
  | (Just ir, Just jr) with (M.lookup ir cls, M.lookup jr cls)
    | (Just ics, Just jcs) = EG
        ()

    | _ = assert_unreachable

insertWith : Semigroup v => (v -> v -> v) -> k -> v -> Map k v -> Map k v
insertWith (+) k v m with (Map.lookup k m)
  | Just v' = Map.insert k (v <+> v') m
  | Nothing = Map.insert k v m

getUsages : List Constr -> Map Evar (List (Set Evar))
getUsages [] = Map.empty
getUsages (CLeq gs q :: cs)
    = insertWith (++) q [gs] $ getUsages cs
getUsages (_ :: cs) = getUsages cs

export
solve : List Constr -> Either ErrMsg Solution
solve c = ?rhs
