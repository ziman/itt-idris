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

namespace Telescope
  public export
  data Telescope : (q : Type) -> (base : Nat) -> (size : Nat) -> Type where
    Nil : Telescope q n Z
    (::) : (b : Binding q (m + n)) -> (ds : Telescope q n m) -> Telescope q n (S m)

  eqTelescopeLen : (xs : Telescope q b s) -> (ys : Telescope q b s') -> Maybe (s = s')
  eqTelescopeLen [] [] = Just Refl
  eqTelescopeLen (x :: xs) (y :: ys) = cong S <$> eqTelescopeLen xs ys
  eqTelescopeLen _ _ = Nothing

  export
  lookupName : Fin pn -> Telescope q n pn -> String
  lookupName FZ (B n q ty :: _) = n
  lookupName (FS i) (_ :: bs) = lookupName i bs

  export
  (++) : Telescope q (s + n) s' -> Telescope q n s -> Telescope q n (s' + s)
  (++) [] ys = ys
  (++) {s} {n} {s' = S s'} (x :: xs) ys =
    replace {p = Binding _} (plusAssociative s' s n) x :: xs ++ ys

mutual
  export
  Eq q => Eq (Binding q n) where
    (==) (B n q ty) (B n' q' ty') =
        (n == n') && (q == q') && (ty == ty')

  export
  Eq q => Eq (Telescope q b s) where
    (==) [] [] = True
    (==) (b :: xs) (b' :: xs') = b == b' && xs == xs'
    (==) _ _ = False

  export
  Eq q => Eq (TT q n) where
    (==) (P n) (P n') = n == n'
    (==) (V i) (V j) = finEq i j
    (==) (Lam b rhs) (Lam b' rhs') = b == b' && rhs == rhs'
    (==) (Pi  b rhs) (Pi  b' rhs') = b == b' && rhs == rhs'
    (==) (App q f x) (App q' f' x')
      = (q == q') && (f == f') && (x == x')
    (==) Type_ Type_ = True
    (==) Erased Erased = True
    _ == _ = False
