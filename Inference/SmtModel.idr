module Inference.SmtModel

import Core.TT
import Utils.Smt
import Inference.Evar
import Inference.Infer

import public Data.SortedMap
import Data.SortedSet

%default total

public export
data Error
  = Unsatisfiable (List Doc)
  | OtherError String

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
    eNumsC (CProdSumLeq lhs rhs) = concatMap (concatMap ev) lhs <+> ev rhs
    eNumsC (CProdEq lhs rhs) = concatMap ev lhs <+> ev rhs
    eNumsC (CProdSumLeqProd lhs rhs) = concatMap (concatMap ev) lhs <+> concatMap ev rhs
    eNumsC (CEq lhs rhs) = ev lhs <+> ev rhs

declVars : SmtType Q -> List ENum -> SmtM Doc (SortedMap ENum (Smt Q))
declVars smtQ [] = pure $ SortedMap.empty
declVars smtQ (n::ns) = SortedMap.insert n <$> declVar ("ev" ++ show n) smtQ <*> declVars smtQ ns

evSmt : SortedMap ENum (Smt Q) -> Evar -> Smt Q
evSmt vs (QQ q) = lit q
evSmt vs (EV i) = case SortedMap.lookup i vs of
  Just v  => v
  Nothing => smtError "cannot-happen"

numberOf : Q -> List (Smt Q) -> Smt Int
numberOf q vs = sum [ifte {a=Int} (v .== lit q) 1 0 | v <- vs]

model : SortedSet ENum -> SortedSet ENum -> List Constr -> SmtM Doc (FList Smt [(ENum, Q)])
model minvs maxvs cs = do
  smtQ <- the (SmtM Doc (SmtType Q)) $ declEnum "Q"
  let allENums = eNums cs <+> minvs <+> maxvs
  ens <- declVars smtQ (SortedSet.toList allENums)
  let ev = evSmt ens

  add <- defineEnumFun2 "add" smtQ smtQ smtQ (.+.)
  mul <- defineEnumFun2 "mul" smtQ smtQ smtQ (.*.)
  leq <- defineEnumFun2 "leq" smtQ smtQ smtBool (.<=.)

  let product = foldMap mul (lit semi1) ev
  let prodSum = foldMap add (lit semi0) product

  for_ cs $ \c =>
    assert (pretty () c) $ case c of
      CProdSumLeqProd lhs rhs => prodSum lhs `leq` product rhs
      CProdSumLeq lhs rhs => prodSum lhs `leq` ev rhs
      CProdEq lhs rhs => product lhs .== ev rhs
      CEq lhs rhs => ev lhs .== ev rhs

  let minvs' = ev . EV <$> toList minvs
  minimise $ numberOf R minvs' + numberOf L minvs'
  minimise $ numberOf R minvs'
  minimise $ numberOf E minvs'
  minimise $ numberOf I minvs'

  let maxvs' = ev . EV <$> toList maxvs
  maximise $ numberOf R maxvs' + numberOf L maxvs'
  maximise $ numberOf R maxvs'
  maximise $ numberOf E maxvs'
  maximise $ numberOf I maxvs'

  pure [SortedMap.toList ens]
 where
  foldMap : (a -> a -> a) -> a -> (b -> a) -> List b -> a
  foldMap op neutr f [] = neutr
  foldMap op neutr f [x] = f x
  foldMap op neutr f (x :: xs) = f x `op` foldMap op neutr f xs

covering export
solve : SortedSet ENum -> SortedSet ENum -> List Constr -> IO (Either Error (SortedMap ENum Q))
solve minvs maxvs cs = do
  sol <- Smt.solve $ model minvs maxvs cs
  pure $ case sol of
    Left (Smt.Unsatisfiable core) => Left (Unsatisfiable core)
    Left e => Left (OtherError $ show e)
    Right [vars] => Right $ SortedMap.fromList vars
