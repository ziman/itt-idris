module Inference.SmtQuick

import Core.TT
import Utils.Smt
import Inference.Evar
import Inference.Infer

import public Data.SortedMap
import Data.SortedSet

%default total
%hide Syntax.PreorderReasoning.Ops.infixl.(~=)
%hide Utils.DepSortedMap.DecOrd.infix.(.<=)

public export
data Error
  = Unsatisfiable (List Doc)
  | OtherError String

toInt : Q -> Int
toInt I = 0
toInt E = 1
toInt L = 2
toInt R = 2

fromInt : Int -> Q
fromInt 0 = I
fromInt 1 = E
fromInt _ = R

eNums : List Constr -> SortedSet ENum
eNums [] = neutral
eNums (c :: cs) = eNumsC c <+> eNums cs
  where
    ev : Evar -> SortedSet ENum
    ev (QQ _) = neutral
    ev (EV i) = SortedSet.insert i neutral

    eNumsC : Constr -> SortedSet ENum
    eNumsC (CProdSumLeq lhs rhs) = concatMap (concatMap ev) lhs <+> ev rhs
    eNumsC (CProdEq lhs rhs) = concatMap ev lhs <+> ev rhs
    eNumsC (CProdSumLeqProd lhs rhs) = concatMap (concatMap ev) lhs <+> concatMap ev rhs
    eNumsC (CEq lhs rhs) = ev lhs <+> ev rhs

litQ : Q -> Smt Int
litQ = lit . toInt

declVars : List ENum -> SmtM Doc (SortedMap ENum (Smt Int))
declVars [] = pure $ SortedMap.empty
declVars (n::ns) = do
  v <- declVar ("ev" ++ show n) smtInt
  assert (text $ show n ++ " >= I") (v .>= litQ I)
  assert (text $ show n ++ " <= R") (v .<= litQ R)
  -- assert (text $ show n ++ " != E") (not (v .== litQ E))

  vs <- declVars ns
  pure (insert n v vs)

evSmt : SortedMap ENum (Smt Int) -> Evar -> Smt Int
evSmt vs (QQ q) = litQ q
evSmt vs (EV i) = case SortedMap.lookup i vs of
  Just v  => v
  Nothing => smtError "cannot-happen"

model : List Constr -> SmtM Doc (FList Smt [(ENum, Int)])
model cs = do
  ens <- declVars (SortedSet.toList $ eNums cs)
  let ev = evSmt ens
  let numberOf = \q : Q => sum
        [ ifte {a=Int} (v .== litQ q) 1 0
        | (i, v) <- SortedMap.toList ens
        ]

  let product = foldMap min (litQ R) ev
  let prodSum = foldMap max (litQ I) product

  for_ cs $ \c =>
    assert (pretty () c) $ case c of
      CProdSumLeqProd lhs rhs => prodSum lhs .<= product rhs
      CProdSumLeq lhs rhs => prodSum lhs .<= ev rhs
      CProdEq lhs rhs => product lhs .== ev rhs
      CEq lhs rhs => ev lhs .== ev rhs

  minimise $ numberOf R
  minimise $ numberOf E
  minimise $ numberOf I

  pure [SortedMap.toList ens]
 where
  foldMap : (a -> a -> a) -> a -> (b -> a) -> List b -> a
  foldMap op neutr f [] = neutr
  foldMap op neutr f [x] = f x
  foldMap op neutr f (x :: xs) = f x `op` foldMap op neutr f xs

covering export
solve : List Constr -> IO (Either Error (SortedMap ENum Q))
solve cs = do
  sol <- Smt.solve $ model cs
  pure $ case sol of
    Left (Smt.Unsatisfiable core) => Left (Unsatisfiable core)
    Left e => Left (OtherError $ show e)
    Right [vars] => Right $ SortedMap.fromList $ map (\(k,v) => (k, fromInt v)) vars
