module ITT.Core

import public Utils.Misc
import public Utils.Pretty
import public Utils.OrdSemiring
import public ITT.Quantity
import public Data.Fin
import Control.Monad.Identity

%default total

public export
data Binder = Lam | Pi | Let

export
Eq Binder where
  (==) Lam Lam = True
  (==) Pi  Pi  = True
  (==) Let Let = True
  (==) _ _ = False

public export
data Abstractness = Variable | Constructor

export
Eq Abstractness where
  (==) Variable Variable = True
  (==) Constructor Constructor = True
  (==) _ _ = False

mutual
  public export
  data Body : Type -> Nat -> Type where
    Abstract : Abstractness -> Body q n
    Term : TT q n -> Body q n

  public export
  record Def (q : Type) (n : Nat) where
    constructor D
    defName : String
    defQ    : q
    defType : TT q n
    defBody : Body q (S n)

  public export
  data Telescope : Type -> Nat -> Nat -> Type where
    Nil : Telescope q n n
    (::) : Def q n -> Telescope q m n -> Telescope q m (S n)

  export
  (++) : Telescope q m n -> Telescope q k m -> Telescope q k n
  (++) [] ys = ys
  (++) (d :: xs) ys = d :: xs ++ ys

  public export
  data Alt : (q : Type) -> (n : Nat) -> (pn : Nat) -> Type where
    CtorCase : (cn : Fin n)
        -> (args : Telescope q pn pm)
        -> CaseTree q n pm
        -> Alt q n pn
    DefaultCase : CaseTree q n pn -> Alt q n pn

  public export
  data CaseTree : (q : Type) -> (n : Nat) -> (pn : Nat) -> Type where
    Leaf : TT q (pn + n) -> CaseTree q n pn
    Case : Fin pn -> List (Alt q n pn) -> CaseTree q n pn

  public export
  data Scrutinees : (q : Type) -> (n : Nat) -> (pn : Nat) -> Type where
    Tree : (retTy : TT q n) -> CaseTree q n pn -> Scrutinees q n pn
    Scrutinee :
        (name : String) -> (sq : q) -> (ty : TT q (pn + n))
        -> (val : TT q n)
        -> (rest : Scrutinees q n (S pn))
        -> Scrutinees q n pn

  public export
  data TT : Type -> Nat -> Type where
    V : (i : Fin n) -> TT q n
    Bind : (b : Binder) -> (d : Def q n) -> (rhs : TT q (S n)) -> TT q n
    App : q -> (f : TT q n) -> (x : TT q n) -> TT q n
    Star : TT q n
    Erased : TT q n
    Match : Scrutinees q n Z -> TT q n

mutual
  export
  Eq q => Eq (Body q n) where
    (==) (Abstract x) (Abstract y) = x == y
    (==) (Term x) (Term y) = x == y
    (==) _ _ = False

  export
  Eq q => Eq (TT q n) where
    (==) (V i) (V j)
      = finEq i j
    (==) (Bind b (D n q ty db) rhs) (Bind b' (D n' q' ty' db') rhs')
      = (b == b') && (q == q') && (ty == ty') && (db == db') && (rhs == rhs')
    (==) (App q f x) (App q' f' x')
      = (q == q') && (f == f') && (x == x')
    (==) Star Star = True
    (==) Erased Erased = True
    _ == _ = False
