module TT

import Utils
import Pretty
import public OrdSemiring
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

export
interface ShowQ q where
  showCol : q -> String
  showApp : q -> String

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

mutual
  export
  showTm : ShowQ q => Context q n -> TT q n -> String
  showTm ctx (V i) = defName (lookupCtx i ctx)
  showTm ctx (Bind Lam d rhs) = "\\" ++ showDef ctx d ++ ". " ++ showTm (d :: ctx) rhs
  showTm ctx (Bind Pi  d rhs) = "(" ++ showDef ctx d ++ ") -> " ++ showTm (d :: ctx) rhs
  showTm ctx (Bind Let d rhs) = "let " ++ showDef ctx d ++ " in " ++ showTm (d :: ctx) rhs
  showTm ctx (App q f x) = showTm ctx f ++ showApp q ++ showTm ctx x
  showTm ctx Star = "Type"
  showTm ctx Erased = "_"

  showDef : ShowQ q => Context q n -> Def q n -> String
  showDef ctx (D n q ty (Abstract _)) = n ++ " " ++ showCol q ++ " " ++ showTm ctx ty  
  showDef ctx (D n q ty (Term tm)) = n ++ " " ++ showCol q ++ " " ++ showTm ctx ty ++ " = " ++ showTm (D n q ty (Abstract Variable) :: ctx) tm

public export
data Q = I | E | L | R

export
Show Q where
  show I = "I"
  show E = "E"
  show L = "L"
  show R = "R"

export
ShowQ () where
  showCol () = ":"
  showApp () = " "

export
ShowQ Q where
  showCol q = ":" ++ show q
  showApp q = " -" ++ show q ++ "- "

export
ShowQ (Maybe Q) where
  showCol Nothing = ":"
  showCol (Just q) = showCol q

  showApp Nothing = " "
  showApp (Just q) = showApp q

qToInt : Q -> Int
qToInt I = 0
qToInt E = 1
qToInt L = 2
qToInt R = 3

export
Eq Q where
  (==) = eqBy qToInt

export
Ord Q where
  compare = compareBy qToInt

namespace Lens
  Traversal : Type -> Type -> Type -> Type -> Type
  Traversal s t a b = (
    {f : Type -> Type} -> Applicative f => (a -> f b) -> s -> f t
  )

  Lens : Type -> Type -> Type
  Lens t a = Traversal t t a a

  ILens : (a -> Type) -> (a -> Type) -> Type
  ILens {a} f g = {x, y : a} -> Traversal (f x) (f y) (g x) (g y)

  mutual
    nonFZS : Applicative t => (Fin n -> t (TT q m)) -> Fin (S n) -> t (TT q (S m))
    nonFZS g  FZ    = pure (V FZ)
    nonFZS g (FS i) = assert_total (runIdentity . ttVars (pure . V . FS) <$> g i)

    bodyVars : Traversal (Body q m) (Body q n) (Fin m) (TT q n)
    bodyVars g (Abstract a) = pure $ Abstract a
    bodyVars g (Term tm) = Term <$> ttVars g tm

    defVars : Traversal (Def q m) (Def q n) (Fin m) (TT q n)
    defVars g (D n q ty b) = D n q <$> ttVars g ty <*> bodyVars (nonFZS g) b

    ttVars : Traversal (TT q m) (TT q n) (Fin m) (TT q n)
    ttVars g (V i) = g i
    ttVars g (Bind b d rhs)
      = Bind b <$> defVars g d <*> ttVars (nonFZS g) rhs
    ttVars g (App q f x)
      = App q <$> ttVars g f <*> ttVars g x
    ttVars g Star = pure Star
    ttVars g Erased = pure Erased

  record Const (a : Type) (b : Type) where
    constructor MkConst
    runConst : a

  Functor (Const a) where
    map f (MkConst x) = MkConst x

  Monoid a => Applicative (Const a) where
    pure _ = MkConst neutral
    (<*>) (MkConst x) (MkConst y) = MkConst (x <+> y)

  fold : Monoid a => (Fin n -> a) -> TT q n -> a
  fold {n} f = runConst . ttVars {n} (MkConst . f)

  subst : (Fin n -> TT q m) -> TT q n -> TT q m
  subst g = runIdentity . ttVars (pure . g)

  rename : (Fin n -> Fin m) -> TT q n -> TT q m
  rename g = subst (V . g)

export
substFZ : TT q n -> Fin (S n) -> TT q n
substFZ tm  FZ    = tm
substFZ tm (FS x) = V x

mapFZ : Fin n -> Fin (S n) -> Fin n
mapFZ i  FZ    = i
mapFZ _ (FS j) = j

interface Strengthen (f : Nat -> Type) where
  strengthen : f (S n) -> Maybe (f n)

Strengthen Fin where
  strengthen  FZ    = Nothing
  strengthen (FS i) = Just i

mutual
  Strengthen (Body q) where
    strengthen b = ?rhs

  Strengthen (Def q) where
    strengthen d = ?rhs

  Strengthen (TT q) where
    strengthen tm = ?rhs

covering export
whnf : Context q n -> TT q n -> TT q n
whnf ctx (V i) with (lookupCtx i ctx)
  | D n q ty (Abstract _) = V i
  -- replace recursive references by reference #i
  | D n q ty (Term body)  = whnf ctx $ rename (mapFZ i) body
whnf ctx (Bind Let d rhs) =
  let rhs' = whnf (d::ctx) rhs
    in case strengthen rhs' of
      Just rhs'' => rhs''
      Nothing    => Bind Let d rhs'
whnf ctx (Bind b d rhs) = Bind b d rhs
whnf ctx (App q f x) with (whnf ctx f)
  | Bind Lam d rhs = whnf ctx $ subst (substFZ $ whnf ctx x) rhs
  | f' = App q f' x
whnf ctx Star = Star
whnf ctx Erased = Erased

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

public export
data NestingLevel
  = NoParens
  | NoAppParens
  | UseParens

nlToInt : NestingLevel -> Int
nlToInt NoParens = 0
nlToInt NoAppParens = 1
nlToInt UseParens = 2

export
Eq NestingLevel where
  (==) = eqBy nlToInt

export
Ord NestingLevel where
  compare = compareBy nlToInt

public export
record PrettyTT where
  constructor PTT
  multiLineLam : Bool
  nestingLevel : NestingLevel

parensFrom : NestingLevel -> NestingLevel -> Doc -> Doc
parensFrom required actual =
  if actual >= required
    then parens
    else id

mutual
  export
  ShowQ q => Pretty (Context q n) (Def q n) where
    pretty ctx (D n dq ty (Abstract _))
      = text n <++> text (showCol dq) <++> pretty (PTT False NoParens, ctx) ty
    pretty ctx d@(D n dq ty (Term tm)) =
      text n <++> text (showCol dq) <++> pretty (PTT False NoParens, ctx) ty
      <++> text "=" <++> pretty (PTT True NoParens, d :: ctx) tm

  export
  ShowQ q => Pretty (PrettyTT, Context q n) (TT q n) where
    pretty (PTT top nl, ctx) (V i) = text . defName $ lookupCtx i ctx
    pretty (PTT True nl,  ctx) (Bind Lam d rhs) = parensFrom NoAppParens nl $
      text "\\" <+> pretty ctx d <+> text "."
      $$ indent (pretty (PTT True NoParens, d::ctx) rhs)
    pretty (PTT False nl, ctx) (Bind Lam d rhs) = parensFrom NoAppParens nl $
      text "\\" <+> pretty ctx d <+> text "."
      <++> pretty (PTT True NoParens, d::ctx) rhs
    pretty (PTT top nl, ctx) (Bind Pi d rhs) = parensFrom NoAppParens nl $
      parens (pretty ctx d)
      <++> text "->" <++> pretty (PTT False NoParens, d::ctx) rhs
    pretty (PTT top nl, ctx) (Bind Let d rhs) = parensFrom NoAppParens nl $
      text "let" <++> pretty ctx d
      $$ indent (text "in" <++> pretty (PTT True NoParens, d::ctx) rhs)
    pretty (PTT top nl, ctx) (App q' f x) = parensFrom UseParens nl $
      pretty (PTT False NoAppParens, ctx) f 
      <+> text (showApp q')
      <+> pretty (PTT False UseParens, ctx) x
    pretty (PTT top nl, ctx) Star = text "Type"
    pretty (PTT top nl, ctx) Erased = text "_"

export
ShowQ q => Pretty () (TT q Z) where
  pretty () = pretty (PTT True NoParens, TT.Nil)

export
ShowQ q => Show (TT q Z) where
  show = render " " . pretty ()
