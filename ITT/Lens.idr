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
  altQ : Traversal (Alt q n pn) (Alt q' n pn) q q'
  altQ g (CtorCase cn args ct) = CtorCase cn <$> telescopeQ g args <*> caseTreeQ g ct
  altQ g (DefaultCase ct) = DefaultCase <$> caseTreeQ g ct

  export
  caseTreeQ : Traversal (CaseTree q n pn) (CaseTree q' n pn) q q'
  caseTreeQ g (Leaf tm) = Leaf <$> ttQ g tm
  caseTreeQ g (Case s alts) = Case s <$> traverse (altQ g) alts

  export
  scrutsQ : Traversal (Scrutinees q n pn) (Scrutinees q' n pn) q q'
  scrutsQ g (Tree rty ct) = Tree <$> ttQ g rty <*> caseTreeQ g ct
  scrutsQ g (Scrutinee n q ty val rest) = Scrutinee n <$> g q <*> ttQ g ty <*> ttQ g val <*> scrutsQ g rest

  export
  ttQ : Traversal (TT q n) (TT q' n) q q'
  ttQ g (V i) = pure $ V i
  ttQ g (Bind b d rhs)
    = Bind b <$> defQ g d <*> ttQ g rhs
  ttQ g (App q f x) = App <$> g q <*> ttQ g f <*> ttQ g x
  ttQ g (Match ss) = Match <$> scrutsQ g ss
  ttQ g Star = pure Star
  ttQ g Erased = pure Erased

mutual
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
  ttVars : Traversal (TT q m) (TT q n) (Fin m) (TT q n)
  ttVars g (V i) = g i
  ttVars g (Bind b d rhs)
    = Bind b <$> defVars g d <*> ttVars (nonFZS g) rhs
  ttVars g (App q f x)
    = App q <$> ttVars g f <*> ttVars g x
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
