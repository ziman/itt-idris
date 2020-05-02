module Inference.SmtModel

import Core.TT
import Utils.Smt
import Inference.Evar
import Inference.Infer

import public Data.SortedMap
import Data.SortedSet

%default total

SmtValue Q where
  smtShow = A . show
  smtRead (A "I") = Just I
  smtRead (A "E") = Just E
  smtRead (A "L") = Just L
  smtRead (A "R") = Just R
  smtRead _ = Nothing

SmtEnum Q where
  smtEnumValues = [I, E, L, R]

eNums : List Constr -> SortedSet ENum
eNums [] = neutral
eNums (c :: cs) = eNumsC c <+> eNums cs
  where
    ev : Evar -> SortedSet ENum
    ev (QQ _) = neutral
    ev (EV i) = SortedSet.insert i neutral

    eNumsC : Constr -> SortedSet ENum
    eNumsC (MkC agg bt gs v) = concat $ map ev (v :: SortedSet.toList gs)

declVars : SmtType Q -> List ENum -> SmtM (SortedMap ENum (Smt Q))
declVars smtQ [] = pure $ SortedMap.empty
declVars smtQ (n::ns) = SortedMap.insert n <$> declVar ("ev" ++ show n) smtQ <*> declVars smtQ ns

evSmt : SortedMap ENum (Smt Q) -> Evar -> Smt Q
evSmt vs (QQ q) = lit q
evSmt vs (EV i) = case SortedMap.lookup i vs of
  Just v  => v
  Nothing => smtError "cannot-happen"

model : List Constr -> SmtM (FList Smt [(ENum, Q)])
model cs = do
  smtQ <- the (SmtM (SmtType Q)) $ declEnum "Q"
  ens <- declVars smtQ (SortedSet.toList $ eNums cs)
  let ev = evSmt ens
  let numberOf = \q : Q => sum
        [ ifte {a=Int} (v .== lit q) 1 0
        | (i, v) <- SortedMap.toList ens
        ]

  add <- defineEnumFun2 "add" smtQ smtQ smtQ (.+.)
  mul <- defineEnumFun2 "mul" smtQ smtQ smtQ (.*.)
  max <- defineEnumFun2 "max" smtQ smtQ smtQ (.\/.)
  leq <- defineEnumFun2 "leq" smtQ smtQ smtBool (.<=.)

  let product = foldMap mul (lit semi1) ev
  let maximum = foldMap max (lit top)   ev
  let prodSum = foldMap add (lit semi0) product
  let prodMax = foldMap max (lit semi0) product

  for_ ccs.sums $ \c =>
    assert $ prodSum c.inputs `leq` ev c.result

  for_ ccs.maxes $ \c =>
    assert $ prodMax c.inputs `leq` ev c.result

  minimise $ numberOf R
  minimise $ numberOf L
  minimise $ numberOf E
  minimise $ numberOf I

  pure [SortedMap.toList ens]
 where
  foldMap : (a -> a -> a) -> a -> (b -> a) -> List b -> a
  foldMap op neutr f [] = neutr
  foldMap op neutr f [x] = f x
  foldMap op neutr f (x :: xs) = f x `op` foldMap op neutr f xs

  ccs : CollectedConstrs
  ccs = collect cs

export
solve : List Constr -> IO (Either String (SortedMap ENum Q))
solve cs = do
  sol <- Smt.solve $ model cs
  pure $ case sol of
    Left err => Left $ show err
    Right [vars] => Right $ SortedMap.fromList vars
