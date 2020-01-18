module ITT.Core

import public Utils.Misc
import public Utils.Pretty
import public Utils.OrdSemiring
import public ITT.Quantity
import public Data.Fin
import public Data.Vect
import Control.Monad.Identity

%default total

public export
data Name = N String Int

export
Eq Name where
  (==) (N x i) (N y j) = (x == y) && (i == j)

export
Ord Name where
  compare (N x i) (N y j) =
    case compare x y of
      EQ => compare i j
      xy => xy

export
Show Name where
  show (N s 0) = s
  show (N s i) = s ++ show i

mutual
  public export
  record Binding (q : Type) (n : Nat) where
    constructor B
    bn : String
    bq : q
    bty : TT q n

  public export
  data Telescope : (q : Type) -> (base : Nat) -> (size : Nat) -> Type where
    Nil : Telescope q n Z
    (::) : (b : Binding q (m + n)) -> (ds : Telescope q n m) -> Telescope q n (S m)

  public export
  data TT : Type -> Nat -> Type where
    V : (i : Fin n) -> TT q n
    Lam : (b : Binding q n) -> (rhs : TT q (S n)) -> TT q n
    Pi  : (b : Binding q n) -> (rhs : TT q (S n)) -> TT q n
    App : q -> (f : TT q n) -> (x : TT q n) -> TT q n
    Star : TT q n
    Erased : TT q n

    Bool_  : TT q n
    If_    : TT q n -> TT q n -> TT q n -> TT q n
    True_  : TT q n
    False_ : TT q n

namespace Telescope
  eqTelescopeLen : (xs : Telescope q b s) -> (ys : Telescope q b s') -> Maybe (s = s')
  eqTelescopeLen [] [] = Just Refl
  eqTelescopeLen (x :: xs) (y :: ys) = cong <$> eqTelescopeLen xs ys
  eqTelescopeLen _ _ = Nothing

  export
  lookupName : Fin pn -> Telescope q n pn -> String
  lookupName FZ (B n q ty :: _) = n
  lookupName (FS i) (_ :: bs) = lookupName i bs

  export
  (++) : Telescope q (s + n) s' -> Telescope q n s -> Telescope q n (s' + s)
  (++) [] ys = ys
  (++) {s} {n} {s' = S s'} (x :: xs) ys = replace (plusAssociative s' s n) x :: xs ++ ys

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
    (==) (V i) (V j)
      = finEq i j
    (==) (Lam b rhs) (Lam b' rhs') = b == b' && rhs == rhs'
    (==) (Pi  b rhs) (Pi  b' rhs') = b == b' && rhs == rhs'
    (==) (App q f x) (App q' f' x')
      = (q == q') && (f == f') && (x == x')
    (==) Star Star = True
    (==) Erased Erased = True
    (==) Bool_ Bool_ = True
    (==) (If_ c t e) (If_ c' t' e') =
        (c == c') && (t == t') && (e == e')
    (==) True_ True_ = True
    (==) False_ False_ = True
    _ == _ = False
