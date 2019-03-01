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

model : List Constr -> SmtM ()
model cs = do
  qty <- the (SmtM (SmtType Q)) $ declEnum "Q"
  for_ {b = ()} (Set.toList $ eNums cs) $ \(EN i) => do
    _ <- declVar ("ev" ++ show i) qty
    pure ()

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
