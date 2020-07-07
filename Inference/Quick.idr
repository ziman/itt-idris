module Inference.Quick

import public Core.TT
import public Core.Globals
import public Core.Quantity
import public Inference.Evar
import public Inference.Constraint
import public Compiler.Config
import public Compiler.Monad
import public Data.SortedMap

import Data.List
import Data.Maybe
import Data.SortedSet

%default total

public export
data Error = Mismatch Q Q

Show Error where
  show (Mismatch p q) = "mismatch: " ++ show (p, q)

toQuick : Evar -> Evar
toQuick (QQ L) = QQ R
toQuick ev = ev

infix 3 ~>
record QConstr where
  constructor (~>)
  lhs : List Evar
  rhs : Evar

splitConstr : Constr -> List QConstr
splitConstr (CProdSumLeq lhs rhs) = [gs ~> rhs | gs <- lhs]
splitConstr (CProdEq lhs rhs) = (lhs ~> rhs) :: [[rhs] ~> g | g <- lhs]
splitConstr (CProdSumLeqProd lhs rhs) = [gs ~> r | gs <- lhs, r <- rhs]
splitConstr (CEq lhs rhs) = [[lhs] ~> rhs, [rhs] ~> rhs]

QConstrs : Type
QConstrs = SortedMap Int (SortedSet Evar, SortedSet Evar)  -- (guards, uses)

Index : Type
Index = SortedMap ENum (SortedSet Int)

number : Int -> List (Int, a) -> List a -> List (Int, a)
number _ acc [] = acc
number i acc (x :: xs) = number (i+1) ((i,x) :: acc) xs

collect : List QConstr -> (QConstrs, Index)
collect cs = (fromList numbered, foldl insertI empty numbered)
  where
    insertC : SortedMap (List Evar) (SortedSet Evar)
      -> QConstr
      -> SortedMap (List Evar) (SortedSet Evar)
    insertC qcs (lhs ~> rhs) = mergeWith (<+>) qcs $
      insert (sort lhs) (insert rhs empty) empty

    numbered : List (Int, (SortedSet Evar, SortedSet Evar))
    numbered =
      number 0 []
      . map (\(gs,us) => (SortedSet.fromList gs, us))
      . SortedMap.toList
      $ foldl insertC empty cs

    insertI : Index -> (Int, (SortedSet Evar, SortedSet Evar)) -> Index
    insertI idx (i, (gs, us)) with (SortedSet.toList gs)
      insertI idx (i, (gs, us)) | [] = idx
      insertI idx (i, (gs, us)) | EV j :: rest =
        insertI (mergeWith (<+>) idx (insert j (insert i empty) empty)) (i, (gs, us)) | rest
      insertI idx (i, (gs, us)) | QQ _ :: rest = insertI idx (i, (gs, us)) | rest

est : SortedMap ENum Q -> Evar -> Q
est vals (QQ q) = q
est vals (EV i) = fromMaybe I $ lookup i vals

lToR : Q -> Q
lToR L = R
lToR q = q

eval : SortedMap ENum Q -> SortedSet Evar -> Q
eval vals = lToR . foldl max I . map (est vals) . SortedSet.toList

covering
step : SortedMap ENum Q -> QConstrs -> Index -> List Int -> Either Error (SortedMap ENum Q)
step vals cs idx todo = do
  updates <- findUpdates empty todo
  if null updates
    then pure vals -- done
    else
      let nextTodo = SortedSet.toList $ concatMap (\i => fromMaybe empty $ lookup i idx) (keys updates)
       in step (mergeLeft updates vals) cs idx nextTodo
  where
    updateVals : SortedMap ENum Q -> Q -> List Evar -> Either Error (SortedMap ENum Q)
    updateVals upds q [] = pure upds
    updateVals upds q (QQ q' :: evs) =
      if q > q'
        then Left $ Mismatch q q'
        else updateVals upds q evs
    updateVals upds q (EV i :: evs) =
      case lookup i upds <|> lookup i vals of
        Nothing => updateVals (insert i q upds) q evs  -- new value
        Just q' =>
          if q > q'
            then updateVals (insert i q upds) q evs  -- bump bound
            else updateVals upds q evs  -- already got at least as much, nothing to do

    findUpdates : SortedMap ENum Q -> List Int -> Either Error (SortedMap ENum Q)
    findUpdates upds [] = pure upds
    findUpdates upds (i :: is) =
      case lookup i cs of
        Nothing => findUpdates upds is  -- should never happen
        Just (gs, us) => do
          upds' <- updateVals upds (eval vals gs) (SortedSet.toList us)
          findUpdates upds' is

covering
solveQuick : Constrs -> Either Error (SortedMap ENum Q)
solveQuick cs =
  let (qcs, idx) = collect $ concatMap splitConstr cs.constrs
    in step empty qcs idx (keys qcs)

covering export
solve : Constrs -> ITT (SortedMap ENum Q)
solve cs =
  case solveQuick (mapQ constrsQ toQuick cs) of
    Left e => throw $ show e
    Right vals => pure vals
