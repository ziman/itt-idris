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

SmtValue Evar where
  smtShow (EV i) = A $ "ev" ++ show i
  smtShow (QQ q) = smtShow q

  smtRead (A s) =
    if "ev" `Strings.isPrefixOf` s
      then assert_total $
        -- we know the prefix has two chars
        Just $ EV (EN (cast . strTail . strTail $ s))
      else QQ <$> smtRead (A s)
  smtRead _ = Nothing

interface Model (a : Type) where
  ModelTy : a -> Type
  model : (x : a) -> Smt (ModelTy x)

Model Q where
  ModelTy _ = Q
  model = lit

Model Evar where
  ModelTy _ = Evar
  model = lit

Model Constr where
  ModelTy _ = Bool
  model (CEq v w) = model v .== model w
  model (CLeq gs v) = ?rhs_2
  model (CConv ctx x y) = ?rhs_3

{-
modelConstr : SortedMap ENum (Smt Q) -> Constr -> SmtM ()
modelConstr ens (CEq v w) = assertEq (lit v) (lit w)
modelConstr ens (CLeq gs v) = ?rhs_2
modelConstr ens (CConv ctx x y) = ?rhs_3
-}

namespace Main
  main : IO ()
  main = putStrLn "hello world"
