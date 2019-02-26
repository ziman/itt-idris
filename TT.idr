module TT

import OrdSemiring
import Data.Fin

%default total

interface Pretty (ctx : Type) a where
  pretty : ctx -> a -> String

public export
data Binder : Type where
  Lam : Binder
  Pi  : Binder

export
Eq Binder where
  (==) Lam Lam = True
  (==) Pi Pi = True
  (==) _ _ = False

Pretty ctx Binder where
  pretty _ Lam = "Lam"
  pretty _ Pi  = "Pi"

mutual
  public export
  record Def (q : Type) (n : Nat) where
    constructor D
    defName : String
    defQ    : q
    defType : TT q n

  public export
  data TT : Type -> Nat -> Type where
    V : (i : Fin n) -> TT q n
    Bind : (b : Binder) -> (d : Def q n) -> (rhs : TT q (S n)) -> TT q n
    App : q -> (f : TT q n) -> (x : TT q n) -> TT q n
    Star : TT q n

export
interface ShowQ q where
  showCol : q -> String
  showApp : q -> String

interface Weaken (f : Nat -> Type) where
  weaken : f n -> f (S n)

iterate' : (f : Nat -> Type) -> ((n : Nat) -> f n -> f (S n)) -> (n : Nat) -> f n -> (m : Nat) -> f (m + n)
iterate' f g n x Z = x
iterate' f g n x (S m) = g (m + n) (iterate' f g n x m)

iterate : {f : Nat -> Type} -> (g : {n : Nat} -> f n -> f (S n)) -> {m, n : Nat} -> f n -> f (m + n)
iterate g x = iterate' _ (\n, x => g x) _ x _

mutual
  Weaken (TT q) where
    weaken (V x) = V $ weaken x
    weaken (Bind b d rhs) = Bind b (weaken d) (weaken rhs)
    weaken (App q f x) = App q (weaken f) (weaken x)
    weaken Star = Star

  Weaken (Def q) where
    weaken (D n q ty) = D n q $ weaken ty

infixl 3 |>
public export
data Context : Type -> Nat -> Type where
  Nil : Context q Z
  (|>) : Context q n -> Def q n -> Context q (S n)

export
lookupCtx : Fin n -> Context q n -> Def q n
lookupCtx  FZ    (_   |> d) = weaken d
lookupCtx (FS k) (ctx |> _) = weaken $ lookupCtx k ctx

mutual
  export
  prettyTm : ShowQ q => Context q n -> TT q n -> String
  prettyTm ctx (V i) = defName (lookupCtx i ctx)
  prettyTm ctx (Bind Lam d rhs) = "\\" ++ prettyDef ctx d ++ ". " ++ prettyTm (ctx |> d) rhs
  prettyTm ctx (Bind Pi  d rhs) = "(" ++ prettyDef ctx d ++ ") -> " ++ prettyTm (ctx |> d) rhs
  prettyTm ctx (App q f x) = prettyTm ctx f ++ showApp q ++ prettyTm ctx x
  prettyTm ctx Star = "Type"

  prettyDef : ShowQ q => Context q n -> Def q n -> String
  prettyDef ctx (D n q ty) = n ++ " " ++ showCol q ++ " " ++ prettyTm ctx ty  

public export
data Q = I | E | L | R

export
Show Q where
  show I = "I"
  show E = "E"
  show L = "L"
  show R = "R"

export
ShowQ Q where
  showCol q = ":" ++ show q
  showApp q = "-" ++ show q ++ "-"

export
Eq Q where
  (==) p q = case (p, q) of
    (I, I) => True
    (E, E) => True
    (L, L) => True
    (R, R) => True
    _ => False

extend : (Fin n -> Fin m) -> Fin (S n) -> Fin (S m)
extend f  FZ    = FZ
extend f (FS x) = FS (f x)

mapVars : (Fin n -> Fin m) -> TT q n -> TT q m
mapVars g (V i) = V (g i)
mapVars g (Bind b (D n q ty) rhs) = Bind b (D n q $ mapVars g ty) (mapVars (extend g) rhs)
mapVars g (App q f x) = App q (mapVars g f) (mapVars g x)
mapVars g Star = Star

unS : (Fin n -> TT q m) -> Fin (S n) -> TT q (S m)
unS f  FZ    = V FZ
unS f (FS x) = mapVars FS $ f x

export
substVars : (Fin n -> TT q m) -> TT q n -> TT q m
substVars g (V i) = g i
substVars g (Bind b (D n q ty) rhs) = Bind b (D n q $ substVars g ty) (substVars (unS g) rhs)
substVars g (App q f x) = App q (substVars g f) (substVars g x)
substVars g Star = Star

export
substTop : TT q n -> Fin (S n) -> TT q n
substTop tm  FZ    = tm
substTop tm (FS x) = V x

covering export
rnf : TT q n -> TT q n
rnf (V i) = V i
rnf (Bind b (D n q ty) rhs) = Bind b (D n q (rnf ty)) (rnf rhs)
rnf (App q f x) =
  case rnf f of
    Bind Lam (D n q ty) rhs => rnf $ substVars (substTop $ rnf x) rhs
    f' => App q f' (rnf x)
rnf  Star = Star

export
OrdSemiring Q where
  semi0 = I
  semi1 = L

  (.+.) p q = case (p, q) of
    (I, q) => q
    (q, I) => q
    (R, q) => R
    (q, R) => R
    (E, L) => L
    (L, E) => L
    (E, E) => E
    (L, L) => R  -- important!

  (.*.) p q = case (p, q) of
    (I, q) => I
    (q, I) => I
    (R, q) => q
    (q, R) => q
    (E, L) => E
    (L, E) => E
    (E, E) => E
    (L, L) => L

  (.<=.) p q = case (p, q) of
    (I, _) => True
    (E, E) => True
    (E, R) => True
    (L, L) => True
    (L, R) => True
    (R, R) => True
    _ => False
