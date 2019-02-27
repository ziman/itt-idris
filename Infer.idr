module Infer

import TT
import OrdSemiring

import Data.SortedSet as Set

Set : Type -> Type
Set = SortedSet

data ENum = EN Int

Eq ENum where
  (==) (EN x) (EN y) = x == y

Ord ENum where
  compare (EN x) (EN y) = compare x y

Show ENum where
  show (EN x) = show x

data Evar = QQ Q | EV ENum

data Constr : Type where
  CEq : (v, w : Evar) -> Constr
  CLeq : (gs : List Evar) -> (v : Evar) -> Constr
  CConv : (ctx : Context Evar n) -> (x, y : TT Evar n) -> Constr
