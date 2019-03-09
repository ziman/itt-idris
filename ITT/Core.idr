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
data Abstractness = Abstract | Concrete

export
Eq Abstractness where
  (==) Abstract Abstract = True
  (==) Concrete Concrete = True
  (==) _ _ = False

public export
data Binder : Abstractness -> Type where
  Lam : Binder Abstract
  Pi  : Binder Abstract
  Let : Binder Concrete

export
eqBinder : {a, a' : Abstractness} -> (b : Binder a) -> (b' : Binder a') -> Maybe (a = a')
eqBinder Lam Lam = Just Refl
eqBinder Pi  Pi  = Just Refl
eqBinder Let Let = Just Refl
eqBinder _ _ = Nothing

mutual
  public export
  data Body : (a : Abstractness) -> (q : Type) -> (n : Nat) -> Type where
    Variable : Body Abstract q n
    Constructor : Body Concrete q n
    Term : TT q n -> Body Concrete q n

  public export
  record Def (a : Abstractness) (q : Type) (n : Nat) where
    constructor D
    defName : String
    defQ    : q
    defType : TT q n
    defBody : Body a q (S n)

  public export
  data Telescope : (q : Type) -> (base : Nat) -> (size : Nat) -> Type where
    Nil : Telescope q n Z
    (::) : (d : Def Abstract q (m + n)) -> (ds : Telescope q n m) -> Telescope q n (S m)

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
    P : Name -> TT q n
    Bind : (b : Binder a) -> (d : Def a q n) -> (rhs : TT q (S n)) -> TT q n
    App : q -> (f : TT q n) -> (x : TT q n) -> TT q n
    Match : (ss : List (TT q n))
        -> (pvs : Telescope q n pn)
        -> (ct : CaseTree q n pn)
        -> TT q n
    Star : TT q n
    Erased : TT q n

eqTelescopeLen : (xs : Telescope q b s) -> (ys : Telescope q b s') -> Maybe (s = s')
eqTelescopeLen [] [] = Just Refl
eqTelescopeLen (x :: xs) (y :: ys) = cong <$> eqTelescopeLen xs ys
eqTelescopeLen _ _ = Nothing

mutual
  export
  Eq q => Eq (Body a q n) where
    (==) Variable Variable = True
    (==) Constructor Constructor = True
    (==) (Term tm) (Term tm') = tm == tm'
    (==) _ _ = False

  export
  Eq q => Eq (Def a q n) where
    (==) (D n q ty b) (D n' q' ty' b') =
        (n == n') && (q == q') && (ty == ty') && (b == b')

  export
  Eq q => Eq (Telescope q b s) where
    (==) [] [] = True
    (==) (d :: xs) (d' :: xs') = d == d' && xs == xs'
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
    (==) (Bind Lam d rhs) (Bind Lam d' rhs') = d == d' && rhs == rhs'
    (==) (Bind Pi  d rhs) (Bind Pi  d' rhs') = d == d' && rhs == rhs'
    (==) (Bind Let d rhs) (Bind Let d' rhs') = d == d' && rhs == rhs'
    (==) (App q f x) (App q' f' x')
      = (q == q') && (f == f') && (x == x')
    (==) (Match ss pvs ct) (Match ss' pvs' ct') with (eqTelescopeLen pvs pvs')
      | Just Refl = assert_total $ (ss == ss') && (pvs == pvs') && (ct == ct')
      | Nothing   = False
    (==) Star Star = True
    (==) Erased Erased = True
    _ == _ = False
