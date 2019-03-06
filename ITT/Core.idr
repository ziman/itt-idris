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
  data TT : Type -> Nat -> Type where
    V : (i : Fin n) -> TT q n
    Bind : (b : Binder) -> (d : Def q n) -> (rhs : TT q (S n)) -> TT q n
    App : q -> (f : TT q n) -> (x : TT q n) -> TT q n
    Star : TT q n
    Erased : TT q n

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

iterate' : (f : Nat -> Type) -> ((n : Nat) -> f n -> f (S n)) -> (n : Nat) -> f n -> (m : Nat) -> f (m + n)
iterate' f g n x Z = x
iterate' f g n x (S m) = g (m + n) (iterate' f g n x m)

iterate : {f : Nat -> Type} -> (g : {n : Nat} -> f n -> f (S n)) -> {m, n : Nat} -> f n -> f (m + n)
iterate g x = iterate' _ (\n, x => g x) _ x _

interface Weaken (f : Nat -> Type) where
  weaken : f n -> f (S n)

mutual
  Weaken (TT q) where
    weaken (V x) = V $ FS x
    weaken (Bind b d rhs) = Bind b (weaken d) (weaken rhs)
    weaken (App q f x) = App q (weaken f) (weaken x)
    weaken Star = Star
    weaken Erased = Erased

  Weaken (Body q) where
    weaken (Abstract a) = Abstract a
    weaken (Term tm) = Term $ weaken tm

  Weaken (Def q) where
    weaken (D n q ty db) = D n q (weaken ty) (weaken db)

public export
data Context : Type -> Nat -> Type where
  Nil : Context q Z
  (::) : Def q n -> Context q n -> Context q (S n)

export
lookupCtx : Fin n -> Context q n -> Def q n
lookupCtx  FZ    (d ::  _ ) = weaken d
lookupCtx (FS k) (_ :: ctx) = weaken $ lookupCtx k ctx
