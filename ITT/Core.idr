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
  data Alt : (q : Type) -> (n : Nat) -> (pn : Nat) -> Type where
    CtorCase : (cn : Name)
        -> (args : Telescope q (pn + n) s)
        -> (ct : CaseTree q n (s + pn))
        -> Alt q n pn
    DefaultCase : (ct : CaseTree q n pn) -> Alt q n pn

  public export
  data CaseTree : (q : Type) -> (n : Nat) -> (pn : Nat) -> Type where
    Leaf : (rhs : TT q (pn + n)) -> CaseTree q n pn
    Case : (s : Fin pn) -> (alts : List (Alt q n pn)) -> CaseTree q n pn

  public export
  data TT : Type -> Nat -> Type where
    V : (i : Fin n) -> TT q n
    G : Name -> TT q n
    Lam : (b : Binding q n) -> (rhs : TT q (S n)) -> TT q n
    Pi  : (b : Binding q n) -> (rhs : TT q (S n)) -> TT q n
    Let : (b : Binding q n) -> (val : TT q (S n)) -> (rhs : TT q (S n)) -> TT q n
    App : q -> (f : TT q n) -> (x : TT q n) -> TT q n
    Match : (pvs : Telescope q n pn)
        -> (ss : Vect pn (TT q n))
        -> (ty : TT q (pn + n))
        -> (ct : CaseTree q n pn)
        -> TT q n
    Star : TT q n
    Erased : TT q n

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
  Eq q => Eq (Alt q n pn) where
    (==) (CtorCase cn args ct) (CtorCase cn' args' ct') with (eqTelescopeLen args args')
      | Just Refl = cn == cn' && args == args' && ct == ct'
      | Nothing   = False
    (==) (DefaultCase ct) (DefaultCase ct')
      = ct == ct'
    (==) _ _ = False

  export
  Eq q => Eq (CaseTree q n pn) where
    (==) (Leaf tm) (Leaf tm') = tm == tm
    (==) (Case s alts) (Case s' alts') = s == s' && assert_total (alts == alts')
    (==) _ _ = False

  export
  Eq q => Eq (TT q n) where
    (==) (V i) (V j)
      = finEq i j
    (==) (G n) (G n') = n == n'
    (==) (Lam b rhs) (Lam b' rhs') = b == b' && rhs == rhs'
    (==) (Pi  b rhs) (Pi  b' rhs') = b == b' && rhs == rhs'
    (==) (Let b val rhs) (Let b' val' rhs') = b == b' && val == val' && rhs == rhs'
    (==) (App q f x) (App q' f' x')
      = (q == q') && (f == f') && (x == x')
    (==) (Match pvs ss ty ct) (Match pvs' ss' ty' ct') with (eqTelescopeLen pvs pvs')
      | Just Refl = assert_total $ (ss == ss') && (ty == ty') && (pvs == pvs') && (ct == ct')
      | Nothing   = False
    (==) Star Star = True
    (==) Erased Erased = True
    _ == _ = False
