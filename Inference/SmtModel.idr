module SmtModel

import ITT.Core
import Utils.Smt
import Inference.Evar
import Inference.Infer

import public Data.SortedMap as Map
import Data.SortedSet as Set

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
    ev (EV i) = Set.insert i neutral

    eNumsC : Constr -> SortedSet ENum
    eNumsC (CEq v w) = ev v <+> ev w
    eNumsC (CLeq _bt gs v) = concat $ map ev (v :: Set.toList gs)

declVars : SmtType Q -> List ENum -> SmtM (SortedMap ENum (Smt Q))
declVars smtQ [] = pure $ Map.empty
declVars smtQ (n::ns) = Map.insert n <$> declVar ("ev" ++ show n) smtQ <*> declVars smtQ ns

evSmt : SortedMap ENum (Smt Q) -> Evar -> Smt Q
evSmt vs (QQ q) = lit q
evSmt vs (EV i) with (Map.lookup i vs)
  | Just v  = v
  | Nothing = smtError "cannot-happen"  -- cannot happen

model : List Constr -> SmtM (FList Smt [(ENum, Q)])
model cs = do
  smtQ <- the (SmtM (SmtType Q)) $ declEnum "Q"
  ens <- declVars smtQ (Set.toList $ eNums cs)
  let ev = evSmt ens
  let numberOf = \q => sum [ifte (v .== lit q) 1 0 | (_i, v) <- Map.toList ens]

  add <- defineEnumFun2 "add" smtQ smtQ smtQ (.+.)
  mul <- defineEnumFun2 "mul" smtQ smtQ smtQ (.*.)
  leq <- defineEnumFun2 "leq" smtQ smtQ smtBool (.<=.)

  let product = foldMap mul (lit semi1) ev
  let prodSum = foldMap add (lit semi0) (product . Set.toList)

  for_ {b = ()} (Map.toList cleqm) $ \(v, gss) =>
    assert $ prodSum gss `leq` ev v

  for_ {b = ()} ceqs $ \(v, w) =>
    assertEq (ev v) (ev w)

  minimise $ numberOf R
  minimise $ numberOf L
  minimise $ numberOf E
  minimise $ numberOf I

  pure [Map.toList ens]
 where
  foldMap : (a -> a -> a) -> a -> (b -> a) -> List b -> a
  foldMap op neutr f [] = neutr
  foldMap op neutr f [x] = f x
  foldMap op neutr f (x :: xs) = f x `op` foldMap op neutr f xs

  cleqs : List (Evar, Set Evar)
  cleqs = cs >>= \c => case c of
    CLeq _bt gs v => [(v, gs)]
    _ => []

  cleqm : SortedMap Evar (List (Set Evar))
  cleqm = foldr (\(v, gs) => Map.mergeWith (++) (Map.insert v [gs] neutral)) neutral cleqs

  ceqs : List (Evar, Evar)
  ceqs = cs >>= \c => case c of
    CEq x y => [(x, y)]
    _ => []

export
solve : List Constr -> IO (Either String (SortedMap ENum Q))
solve cs = do
  sol <- Smt.solve $ model cs
  pure $ case sol of
    Left err => Left $ show err
    Right [vars] => Right $ Map.fromList vars
