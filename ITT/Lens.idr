module ITT.Lens

import public ITT.Core
import Control.Monad.Identity

-- %default total

public export
Traversal : Type -> Type -> Type -> Type -> Type
Traversal s t a b = (
  {f : Type -> Type} -> Applicative f => (a -> f b) -> s -> f t
)

public export
Lens : Type -> Type -> Type
Lens t a = Traversal t t a a

public export
ILens : (a -> Type) -> (a -> Type) -> Type
ILens {a} f g = {x, y : a} -> Traversal (f x) (f y) (g x) (g y)

mutual
  export
  bodyQ : Traversal (Body a q n) (Body a q' n) q q'
  bodyQ g Variable = pure Variable
  bodyQ g Constructor = pure Constructor
  bodyQ g (Term tm) = Term <$> ttQ g tm

  export
  defQ : Traversal (Def a q n) (Def a q' n) q q'
  defQ g (D n q ty b) = D n <$> g q <*> ttQ g ty <*> bodyQ g b

  export
  telescopeQ : Traversal (Telescope q b s) (Telescope q' b s) q q'
  telescopeQ g [] = pure []
  telescopeQ g (d :: ds) = (::) <$> defQ g d <*> telescopeQ g ds

  export
  altQ : Traversal (Alt q n pn) (Alt q' n pn) q q'
  altQ g (CtorCase cn args ct) = CtorCase cn <$> telescopeQ g args <*> caseTreeQ g ct
  altQ g (DefaultCase ct) = DefaultCase <$> caseTreeQ g ct

  export
  caseTreeQ : Traversal (CaseTree q n pn) (CaseTree q' n pn) q q'
  caseTreeQ g (Leaf tm) = Leaf <$> ttQ g tm
  caseTreeQ g (Case s alts) = Case s <$> assert_total (traverse (altQ g) alts)

  export
  ttQ : Traversal (TT q n) (TT q' n) q q'
  ttQ g (V i) = pure $ V i
  ttQ g (Bind Lam d rhs) = Bind Lam <$> defQ g d <*> ttQ g rhs
  ttQ g (Bind Pi  d rhs) = Bind Pi  <$> defQ g d <*> ttQ g rhs
  ttQ g (Bind Let d rhs) = Bind Let <$> defQ g d <*> ttQ g rhs
  ttQ g (App q f x) = App <$> g q <*> ttQ g f <*> ttQ g x
  ttQ g (Match ss pvs ct)
    = Match
        <$> assert_total (traverse (ttQ g) ss)
        <*> telescopeQ g pvs
        <*> caseTreeQ g ct
  ttQ g Star = pure Star
  ttQ g Erased = pure Erased

mutual
  private
  nonFZS : Applicative t => (Fin n -> t (TT q m)) -> Fin (S n) -> t (TT q (S m))
  nonFZS g  FZ    = pure (V FZ)
  nonFZS g (FS i) = assert_total (runIdentity . ttVars (pure . V . FS) <$> g i)

  private
  nonTel : Applicative t => (Fin n -> t (TT q m)) -> Telescope q n s -> Fin (s + n) -> t (TT q (s + m))
  nonTel g []        f = ?rhs_1
  nonTel g (_ :: ds) f = ?rhs_2

  export
  bodyVars : Traversal (Body a q m) (Body a q n) (Fin m) (TT q n)
  bodyVars g Variable = pure Variable
  bodyVars g Constructor = pure Constructor
  bodyVars g (Term tm) = Term <$> ttVars g tm

  export
  defVars : Traversal (Def a q m) (Def a q n) (Fin m) (TT q n)
  defVars g (D n q ty b) = D n q <$> ttVars g ty <*> bodyVars (nonFZS g) b

  export
  telescopeVars : Applicative t
    => (Fin m -> t (TT q n))
    -> Telescope q m s
    -> (t (Telescope q n s), Fin (s + m) -> t (TT q (s + n)))
  telescopeVars g [] = (pure [], g)
  telescopeVars g (d :: ds) with (telescopeVars g ds)
    | (ds', g') = ((::) <$> defVars g' d <*> ds', nonFZS g')

  export
  altVars : Applicative t => (Fin m -> t (TT q n)) -> Alt q m pn -> t (Alt q n pn)
  altVars g (DefaultCase ct) = DefaultCase <$> caseTreeVars g ct
  altVars {t} {m} {q} {n} {pn} g (CtorCase {s = s} cn args ct) = ?rhsA
  {-
    where
      args' : t (Telescope q n pn)
      args' = fst $ telescopeVars {m = pn + m} {n = pn + n} {s = s} ?rhsG args
-}

  export
  caseTreeVars : Traversal (CaseTree q m pn) (CaseTree q n pn) (Fin m) (TT q n)
  caseTreeVars g (Leaf tm) = ?rhs -- Leaf <$> ttVars g tm  -- patvars enter context here
  caseTreeVars g (Case s alts) = Case s <$> traverse (altVars g) alts

  export
  ttVars : Traversal (TT q m) (TT q n) (Fin m) (TT q n)
  ttVars g (V i) = g i
  ttVars g (Bind Lam d rhs) = Bind Lam <$> defVars g d <*> ttVars (nonFZS g) rhs
  ttVars g (Bind Pi  d rhs) = Bind Pi  <$> defVars g d <*> ttVars (nonFZS g) rhs
  ttVars g (Bind Let d rhs) = Bind Let <$> defVars g d <*> ttVars (nonFZS g) rhs
  ttVars g (App q f x)
    = App q <$> ttVars g f <*> ttVars g x
  ttVars g (Match ss pvs ct)
    = Match
        <$> assert_total (traverse (ttVars g) ss)
        <*> fst (telescopeVars g pvs)
        <*> caseTreeVars g ct
  ttVars g Star = pure Star
  ttVars g Erased = pure Erased

export
fold : Monoid a => (Fin n -> a) -> TT q n -> a
fold {n} f = runConst . ttVars {n} (MkConst . f)

export
subst : (Fin n -> TT q m) -> TT q n -> TT q m
subst g = runIdentity . ttVars (pure . g)

export
rename : (Fin n -> Fin m) -> TT q n -> TT q m
rename g = subst (V . g)

export
renameDef : (Fin n -> Fin m) -> Def a q n -> Def a q m
renameDef g = runIdentity . defVars (pure . V . g)
