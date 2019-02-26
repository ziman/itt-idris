module TT

import Data.Fin
import Data.Vect
import Data.List

%default total

interface Pretty (ctx : Type) a where
  pretty : ctx -> a -> String

data Binder : Type where
  Lam : Binder
  Pi  : Binder

Pretty ctx Binder where
  pretty _ Lam = "Lam"
  pretty _ Pi  = "Pi"

mutual
  record Def (q : Type) (n : Nat) where
    constructor D
    defName : String
    defQ    : q
    defType : TT q n

  data TT : Type -> Nat -> Type where
    V : (i : Fin n) -> TT q n
    Bind : (b : Binder) -> (d : Def q n) -> (rhs : TT q (S n)) -> TT q n
    App : q -> (f : TT q n) -> (x : TT q n) -> TT q n
    Star : TT q n

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
data Context : Type -> Nat -> Type where
  Nil : Context q Z
  (|>) : Context q n -> Def q n -> Context q (S n)

ixCtx : Fin n -> Context q n -> Def q n
ixCtx  FZ    (_   |> d) = weaken d
ixCtx (FS k) (ctx |> _) = weaken $ ixCtx k ctx

mutual
  prettyTm : ShowQ q => Context q n -> TT q n -> String
  prettyTm ctx (V i) = defName (ixCtx i ctx)
  prettyTm ctx (Bind Lam d rhs) = "\\" ++ prettyDef ctx d ++ ". " ++ prettyTm (ctx |> d) rhs
  prettyTm ctx (Bind Pi  d rhs) = "(" ++ prettyDef ctx d ++ ") -> " ++ prettyTm (ctx |> d) rhs
  prettyTm ctx (App q f x) = prettyTm ctx f ++ showApp q ++ prettyTm ctx x
  prettyTm ctx Star = "Type"

  prettyDef : ShowQ q => Context q n -> Def q n -> String
  prettyDef ctx (D n q ty) = n ++ " " ++ showCol q ++ " " ++ prettyTm ctx ty  

data Q = I | E | L | R

Show Q where
  show I = "I"
  show E = "E"
  show L = "L"
  show R = "R"

ShowQ Q where
  showCol q = ":" ++ show q
  showApp q = "-" ++ show q ++ "-"

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

subst : (Fin n -> TT q m) -> TT q n -> TT q m
subst g (V i) = g i
subst g (Bind b (D n q ty) rhs) = Bind b (D n q $ subst g ty) (subst (unS g) rhs)
subst g (App q f x) = App q (subst g f) (subst g x)
subst g Star = Star

substTop : TT q n -> Fin (S n) -> TT q n
substTop tm  FZ    = tm
substTop tm (FS x) = V x

partial
rnf : TT q n -> TT q n
rnf (V i) = V i
rnf (Bind b (D n q ty) rhs) = Bind b (D n q (rnf ty)) (rnf rhs)
rnf (App q f x) =
  case rnf f of
    Bind Lam (D n q ty) rhs => rnf $ subst (substTop $ rnf x) rhs
    f' => App q f' (rnf x)
rnf  Star = Star
