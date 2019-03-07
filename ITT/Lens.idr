module ITT.Lens

import public ITT.Core
import Control.Monad.Identity

%default total

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
  bodyQ : Traversal (Body q n) (Body q' n) q q'
  bodyQ g (Abstract a) = pure $ Abstract a
  bodyQ g (Term tm) = Term <$> ttQ g tm

  export
  defQ : Traversal (Def q n) (Def q' n) q q'
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
  ttQ g (Bind b d rhs)
    = Bind b <$> defQ g d <*> ttQ g rhs
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

  export
  bodyVars : Traversal (Body q m) (Body q n) (Fin m) (TT q n)
  bodyVars g (Abstract a) = pure $ Abstract a
  bodyVars g (Term tm) = Term <$> ttVars g tm

  export
  defVars : Traversal (Def q m) (Def q n) (Fin m) (TT q n)
  defVars g (D n q ty b) = D n q <$> ttVars g ty <*> bodyVars (nonFZS g) b

  export
  telescopeVars : Traversal (Telescope q m s) (Telescope q n s) (Fin m) (TT q n)
  telescopeVars g [] = pure []
  telescopeVars g (d :: ds) = ?rhs --  (::) <$> defVars g d <*> telescopeVars (nonFZS g) ds

  export
  altVars : Traversal (Alt q m pn) (Alt q n pn) (Fin m) (TT q n)
  altVars g (DefaultCase ct) = DefaultCase <$> caseTreeVars g ct
  altVars g (CtorCase cn args ct)
    = CtorCase
        <$> ?cn  -- we probably need a separate index/scope for constructors
        <*> telescopeVars g args
        <*> caseTreeVars g ct

  export
  caseTreeVars : Traversal (CaseTree q m pn) (CaseTree q n pn) (Fin m) (TT q n)
  caseTreeVars g (Leaf tm) = Leaf <$> ttVars g tm
  caseTreeVars g (Case s alts) = Case s <$> traverse (altVars g) alts

  export
  ttVars : Traversal (TT q m) (TT q n) (Fin m) (TT q n)
  ttVars g (V i) = g i
  ttVars g (Bind b d rhs)
    = Bind b <$> defVars g d <*> ttVars (nonFZS g) rhs
  ttVars g (App q f x)
    = App q <$> ttVars g f <*> ttVars g x
  ttVars g (Match ss pvs ct)
    = Match
        <$> assert_total (traverse (ttVars g) ss)
        <*> telescopeVars g pvs
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
renameDef : (Fin n -> Fin m) -> Def q n -> Def q m
renameDef g = runIdentity . defVars (pure . V . g)
