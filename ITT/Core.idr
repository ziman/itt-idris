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

public export
data Abstractness = Variable | Constructor

export
Eq Abstractness where
  (==) Variable Variable = True
  (==) Constructor Constructor = True
  (==) _ _ = False

public export
record NoBody (q : Type) (n : Nat) where
  constructor MkNoBody

public export
Eq (NoBody q n) where
  (==) _ _ = True

mutual
  public export
  data Body : (q : Type) -> (n : Nat) -> Type where
    Abstract : Abstractness -> Body q n
    Term : TT q n -> Body q n

  public export
  record Def (bty : Type -> Nat -> Type) (q : Type) (n : Nat) where
    constructor D
    defName : String
    defQ    : q
    defType : TT q n
    defBody : bty q (S n)

  public export
  data Telescope
    : (bty : Type -> Nat -> Type)
    -> (q : Type)
    -> (base : Nat)
    -> (size : Nat)
    -> Type where

    Nil : Telescope bty q n Z
    (::) : (d : Def bty q (m + n)) -> (ds : Telescope bty q n m) -> Telescope bty q n (S m)

  export
  (++) : Telescope bty q (m + n) k
    -> Telescope bty q n m
    -> Telescope bty q n (k + m)
  (++) [] ys = ys
  (++) (d :: xs) ys = replace {P = Def _ _} (plusAssociative _ _ _) d :: xs ++ ys

  public export
  data Alt : (q : Type) -> (n : Nat) -> (pn : Nat) -> Type where
    CtorCase : (cn : Fin n)
        -> (args : Telescope NoBody q (pn + n) pm)
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
    Lam : (d : Def NoBody q n)
        -> (rhs : TT q (S n))
        -> TT q n
    Pi : (d : Def NoBody q n)
        -> (rhs : TT q (S n))
        -> TT q n
    Let : (d : Def NoBody q n)
        -> (val : TT q (S n))  -- recursive
        -> (rhs : TT q (S n))
        -> TT q n
    App : q -> (f : TT q n) -> (x : TT q n) -> TT q n
    Match : (ss : List (TT q n))
        -> (pvs : Telescope NoBody q n pn)
        -> (ct : CaseTree q n pn)
        -> TT q n
    Star : TT q n
    Erased : TT q n

eqTelescopeLen : (xs : Telescope bty q b s) -> (ys : Telescope bty q b s') -> Maybe (s = s')
eqTelescopeLen [] [] = Just Refl
eqTelescopeLen (x :: xs) (y :: ys) = cong <$> eqTelescopeLen xs ys
eqTelescopeLen _ _ = Nothing

mutual
  export
  (Eq q, (Eq (bty q (S n)))) => Eq (Def bty q n) where
    (==) (D n q ty b) (D n' q' ty' b') =
        (n == n') && (q == q') && (ty == ty') && (b == b')

  export
  (Eq q, (n' : Nat) -> Eq (bty q n')) => Eq (Telescope bty q b s) where
    (==) [] [] = True
    (==) (d :: xs) (d' :: xs') = ?rhsA
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
    (==) (Lam d rhs) (Lam  d' rhs') = d == d' && rhs == rhs'
    (==) (Pi  d rhs) (Pi   d' rhs') = d == d' && rhs == rhs'
    (==) (Let d val rhs) (Let d' val' rhs') = d == d' && val == val' && rhs == rhs'
    (==) (App q f x) (App q' f' x')
      = (q == q') && (f == f') && (x == x')
    (==) (Match ss pvs ct) (Match ss' pvs' ct') with (eqTelescopeLen pvs pvs')
      | Just Refl = assert_total $ (ss == ss') && (pvs == pvs') && (ct == ct')
      | Nothing   = False
    (==) Star Star = True
    (==) Erased Erased = True
    _ == _ = False
