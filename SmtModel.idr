module SmtModel

import TT
import Smt
import Infer

import Data.SortedMap as Map
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
    eNumsC (CLeq gs v) = concat $ map ev (v :: Set.toList gs)
    eNumsC (CConv ctx x y) = neutral

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

  add <- defineEnumFun2 "add" smtQ smtQ smtQ (.+.)
  mul <- defineEnumFun2 "mul" smtQ smtQ smtQ (.*.)
  leq <- defineEnumFun2 "leq" smtQ smtQ smtBool (.<=.)

  for_ {b = ()} (Map.toList cleqm) $ \(v, gss) =>
    assert $
      (foldMap add
        (lit semi0)
        (foldMap mul (lit semi1) ev . Set.toList)
        gss)
      `leq` ev v

  for_ {b = ()} ceqs $ \(v, w) =>
    assertEq (ev v) (ev w)

  pure [Map.toList ens]
 where
  foldMap : (a -> a -> a) -> a -> (b -> a) -> List b -> a
  foldMap op neutr f [] = neutr
  foldMap op neutr f [x] = f x
  foldMap op neutr f (x :: xs) = f x `op` foldMap op neutr f xs

  cleqs : List (Evar, Set Evar)
  cleqs = cs >>= \c => case c of
    CLeq gs v => [(v, gs)]
    _ => []

  cleqm : SortedMap Evar (List (Set Evar))
  cleqm = foldr (\(v, gs) => Map.mergeWith (++) (Map.insert v [gs] neutral)) neutral cleqs

  ceqs : List (Evar, Evar)
  ceqs = cs >>= \c => case c of
    CEq x y => [(x, y)]
    _ => []

namespace Main
  main : IO ()
  main = do
      sol <- Smt.solve $ model cs
      case sol of
        Left err     => printLn err
        Right [vars] => printLn vars
    where
      cs =
            [ CEq (QQ I) (EV $ EN 0)
            , CLeq (Set.fromList [EV $ EN 0, EV $ EN 1, QQ L]) (EV $ EN 2)
            ]
