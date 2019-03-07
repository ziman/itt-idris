module ITT.Core

import public Utils.Misc
import public Utils.Pretty
import public Utils.OrdSemiring
import public ITT.Quantity
import public Data.Fin
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
  data Binder : Type -> Nat -> Type where
    Lam : Def q () n -> Binder q n
    Pi  : Def q () n -> Binder q n
    Let : Def q (TT q n) n -> Binder q n

  public export
  record Def (q : Type) (bty : Type) (n : Nat) where
    constructor D
    defName : String
    defQ    : q
    defType : TT q n
    defBody : bty

  public export
  data Telescope : Type -> (base : Nat) -> (size : Nat) -> Type where
    Nil : Telescope q n Z
    (::) : (d : Def q () (m + n)) -> (ds : Telescope q n m) -> Telescope q n (S m)

  export
  (++) : Telescope q (m + n) k -> Telescope q n m -> Telescope q n (k + m)
  (++) [] ys = ys
  (++) (d :: xs) ys = replace {P = Def _ _} (plusAssociative _ _ _) d :: xs ++ ys

  public export
  data Alt : (q : Type) -> (n : Nat) -> (pn : Nat) -> Type where
    CtorCase : (cn : Fin n)
        -> (args : Telescope q (pn + n) pm)
        -> (ct : CaseTree q n (pm + pn))
        -> Alt q n pn
    DefaultCase : (ct : CaseTree q n pn) -> Alt q n pn

  public export
  data CaseTree : (q : Type) -> (n : Nat) -> (pn : Nat) -> Type where
    Leaf : (rhs : TT q (pn + n)) -> CaseTree q n pn
    Case : (s : Fin pn) -> (alts : List (Alt q n pn)) -> CaseTree q n pn

  public export
  data TT : Type -> Nat -> Type where
    V : (i : Fin n) -> TT q n
    P : Name -> TT q n
    Bind : (b : Binder q n) -> (rhs : TT q (S n)) -> TT q n
    App : q -> (f : TT q n) -> (x : TT q n) -> TT q n
    Match : (ss : List (TT q n))
        -> (pvs : Telescope q n pn)
        -> (ct : CaseTree q n pn)
        -> TT q n
    Star : TT q n
    Erased : TT q n

mutual
  export
  Eq bty => Eq (Def q bty n) where
    (==) (D n q ty b) (D n' q' ty' b') = (n == n') && (q == q') && (ty == ty') && (b == b')

  export
  Eq (Binder q n) where
    (==) (Lam d) (Lam d') = (d == d')
    (==) (Pi  d) (Pi  d') = (d == d')
    (==) (Let d) (Let d') = (d == d')
    (==) _ _ = False

  export
  Eq q => Eq (TT q n) where
    (==) (V i) (V j)
      = finEq i j
    (==) (Bind b rhs) (Bind b' rhs')
      = (b == b') && (rhs == rhs')
    (==) (App q f x) (App q' f' x')
      = (q == q') && (f == f') && (x == x')
    (==) Star Star = True
    (==) Erased Erased = True
    _ == _ = False
