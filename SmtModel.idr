module SmtModel

import TT
import Smt
import Infer

import Data.SortedMap as Map
import Data.SortedSet as Set

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

SmtEnum Q where
  smtEnumValues = [I, E, L, R]

SmtValue Evar where
  smtShow (EV i) = A $ "ev" ++ show i
  smtShow (QQ q) = smtShow q

  smtRead (A s) =
    if "ev" `Strings.isPrefixOf` s
      then Just $ EV (EN (cast . strTail . strTail $ s))
      else QQ <$> smtRead (A s)
  smtRead _ = Nothing

modelConstr : SortedMap ENum (Smt Q) -> Constr -> SmtM ()
modelConstr ens constr = ?rhs

namespace Main
  main : IO ()
  main = putStrLn "hello world"
