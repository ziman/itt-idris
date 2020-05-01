module Core.TT

import public Utils.Misc
import public Utils.Pretty
import public Utils.OrdSemiring
import public Core.Quantity
import public Data.Nat
import public Data.Fin
import public Data.Vect
import Control.Monad.Identity

%default total
%undotted_record_projections off

public export
data Name
  = UN String
  | MN String Int

export
Eq Name where
  (==) (UN x) (UN y) = x == y
  (==) (MN x i) (MN y j) = (x == y) && (i == j)
  (==) _ _ = False

export
Ord Name where
  compare (MN x i) (MN y j) =
    case compare x y of
      EQ => compare i j
      xy => xy
  compare (UN x) (UN y) = compare x y
  compare (UN _) (MN _ _) = LT
  compare (MN _ _) (UN _) = GT

export
Show Name where
  show (UN s) = s
  show (MN s i) = "{" ++ s ++ show i ++ "}"

mutual
  public export
  record Binding (q : Type) (n : Nat) where
    constructor B
    name : String
    qv : q
    type : TT q n

  public export
  data TT : Type -> Nat -> Type where
    P : (gn : Name) -> TT q n
    V : (i : Fin n) -> TT q n
    Lam : (b : Binding q n) -> (rhs : TT q (S n)) -> TT q n
    Pi  : (b : Binding q n) -> (rhs : TT q (S n)) -> TT q n
    App : q -> (f : TT q n) -> (x : TT q n) -> TT q n
    Type_ : TT q n
    Erased : TT q n
