module Core.TT

import public Utils.Misc
import public Utils.Pretty
import public Utils.OrdSemiring
import public Utils.DepSortedMap
import public Core.Quantity
import public Data.Nat
import public Data.Fin
import public Data.Vect

import Decidable.Equality
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

public export
data MetaNum = MNValue Int | MNType Int | MNUnknown

export
Eq MetaNum where
  MNValue i == MNValue j = i == j
  MNType i == MNType j = i == j
  MNUnknown == MNUnknown = True
  _ == _ = False

export
Ord MetaNum where
  compare (MNValue i) (MNValue j) = compare i j
  compare (MNValue _) _ = LT
  compare (MNType i) (MNValue _) = GT
  compare (MNType i) (MNType j) = compare i j
  compare (MNType _) MNUnknown = LT
  compare MNUnknown MNUnknown = EQ
  compare MNUnknown _ = GT

export
DecEq MetaNum where
  decEq (MNValue i) (MNValue j) with (decEq i j)
    decEq (MNValue i) (MNValue i) | Yes Refl = Yes Refl
    decEq (MNValue i) (MNValue j) | No contra = No $ \case Refl => contra Refl
  decEq (MNType i) (MNType j) with (decEq i j)
    decEq (MNType i) (MNType i) | Yes Refl = Yes Refl
    decEq (MNType i) (MNType j) | No contra = No $ \case Refl => contra Refl
  decEq MNUnknown MNUnknown = Yes Refl
  decEq (MNValue i) (MNType j) = No $ \case Refl impossible
  decEq (MNValue i) MNUnknown = No $ \case Refl impossible
  decEq (MNType i) (MNValue j) = No $ \case Refl impossible
  decEq (MNType i) MNUnknown = No $ \case Refl impossible
  decEq MNUnknown (MNType i) = No $ \case Refl impossible
  decEq MNUnknown (MNValue i) = No $ \case Refl impossible

export
DecOrd MetaNum where
  decCmp (MNValue i) (MNValue j) with (decCmp i j)
    decCmp (MNValue i) (MNValue j) | LT = LT
    decCmp (MNValue i) (MNValue i) | EQ Refl = EQ Refl
    decCmp (MNValue i) (MNValue j) | GT = GT
  decCmp (MNValue _) _ = LT
  decCmp (MNType i) (MNValue _) = GT
  decCmp (MNType i) (MNType j) with (decCmp i j)
    decCmp (MNType i) (MNType j) | LT = LT
    decCmp (MNType i) (MNType i) | EQ Refl = EQ Refl
    decCmp (MNType i) (MNType j) | GT = GT
  decCmp (MNType _) MNUnknown = LT
  decCmp MNUnknown MNUnknown = EQ Refl
  decCmp MNUnknown _ = GT

export
Show MetaNum where
  show (MNValue i) = "_" ++ show i
  show (MNType i) = "_ty" ++ show i
  show MNUnknown = "_"

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
    Meta : MetaNum -> TT q n

mutual
  export
  Eq q => Eq (Binding q n) where
    B n q ty == B n' q' ty' = (n == n') && (q == q') && (ty == ty')

  export
  Eq q => Eq (TT q n) where
    P m == P n = m == n
    V i == V j = i == j
    Lam b rhs == Lam b' rhs' = (b == b') && (rhs == rhs')
    Pi b rhs == Pi b' rhs' = (b == b') && (rhs == rhs')
    App q f x == App q' f' x' = (q == q') && (f == f') && (x == x')
    Type_ == Type_ = True
    Erased == Erased = True
    Meta i == Meta j = i == j
    _ == _ = False
