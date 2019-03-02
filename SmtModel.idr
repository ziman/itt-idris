module SmtModel

import TT
import Smt
import Infer

import Data.SortedMap as Map
import Data.SortedSet as Set

%default total

{-
data Constr : Type where
  CEq : (v, w : Evar) -> Constr
  CLeq : (gs : Set Evar) -> (v : Evar) -> Constr
  CConv : (ctx : Context Evar n) -> (x, y : TT Evar n) -> Constr
-}

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

{-
modelConstr : SortedMap ENum (Smt Q) -> Constr -> Prop
modelConstr vs c = case c of
    (CEq v w) => ev v .== ev w
    (CLeq gs v) => foldr add (Set.toList gs) 
    (CConv ctx x y) => ?rhs_3
  where
    ev : Evar -> Smt Q
    ev (QQ q) = lit q
    ev (EV i) with (Map.lookup i vs)
      | Just v  = v
      | Nothing = smtError "cannot-happen"  -- cannot happen
-}

evSmt : SortedMap ENum (Smt Q) -> Evar -> Smt Q
evSmt vs (QQ q) = lit q
evSmt vs (EV i) with (Map.lookup i vs)
  | Just v  = v
  | Nothing = smtError "cannot-happen"  -- cannot happen

model : List Constr -> SmtM ()
model cs = do
  smtQ <- the (SmtM (SmtType Q)) $ declEnum "Q"
  ev  <- evSmt <$> declVars smtQ (Set.toList $ eNums cs)

  add <- defineEnumFun2 "add" smtQ smtQ smtQ (.+.)
  mul <- defineEnumFun2 "mul" smtQ smtQ smtQ (.*.)
  leq <- defineEnumFun2 "leq" smtQ smtQ smtBool (.<=.)

  for_ {b = ()} (Map.toList cleqm) $ \(v, gss) =>
    assert $
      (foldr
        (\gs => add
          (foldr (mul . ev) (lit semi1) $ Set.toList gs))
        (lit semi0)
        gss)
      `leq` ev v

  pure ()
 where
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
  main = case runSmtM $ model cs of
      Left err => printLn err
      Right src => putStrLn src
    where
      cs =
            [ CEq (QQ I) (EV $ EN 0)
            , CLeq (Set.fromList [EV $ EN 0, EV $ EN 1, QQ L]) (EV $ EN 2)
            ]
