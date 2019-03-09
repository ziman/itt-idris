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
  varDefQ : Traversal (VarDef q n) (VarDef q' n) q q'
  varDefQ g (VD n q ty) = VD n <$> g q <*> ttQ g ty

  export
  telescopeQ : Traversal (Telescope q b s) (Telescope q' b s) q q'
  telescopeQ g [] = pure []
  telescopeQ g (d :: ds) = (::) <$> varDefQ g d <*> telescopeQ g ds

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
  ttQ g (Lam d rhs) = Lam <$> varDefQ g d <*> ttQ g rhs
  ttQ g (Pi  d rhs) = Pi  <$> varDefQ g d <*> ttQ g rhs
  ttQ g (Let d val rhs) = Let <$> varDefQ g d <*> ttQ g val <*> ttQ g rhs
  ttQ g (App q f x) = App <$> g q <*> ttQ g f <*> ttQ g x
  ttQ g (Match ss pvs ct)
    = Match
        <$> assert_total (traverse (ttQ g) ss)
        <*> telescopeQ g pvs
        <*> caseTreeQ g ct
  ttQ g Star = pure Star
  ttQ g Erased = pure Erased

mutual
  -- split references between those that point into the telescope
  -- and those that point beyond it
  splitFin : Telescope q n' s -> Fin (s + n) -> Either (Fin s) (Fin n)
  splitFin [] f = Right f
  splitFin (d :: ds)  FZ    = Left FZ
  splitFin (d :: ds) (FS i) with (splitFin ds i)
    | Left  j = Left  (FS j)
    | Right j = Right j

  -- push all references to point beyond the telescope
  tackFinR : Telescope q n' s -> Fin n -> Fin (s + n)
  tackFinR []        f = f
  tackFinR (d :: ds) f = FS $ tackFinR ds f

  -- repeated weakening, identity at runtime
  tackFinL : Fin s -> Fin (s + n)
  tackFinL  FZ    = FZ
  tackFinL (FS i) = FS $ tackFinL i

  export
  skipFZ : Applicative t => (Fin n -> t (TT q m)) -> Fin (S n) -> t (TT q (S m))
  skipFZ g  FZ    = pure (V FZ)
  skipFZ g (FS i) = rename FS <$> g i

  export
  -- this could be expressed as iterated skipFZ
  -- but that would traverse the term repeatedly
  -- so let's just do it in one pass using splitFin and tackFin
  skipTel : Applicative t => Telescope q n s -> (Fin n -> t (TT q m)) -> Fin (s + n) -> t (TT q (s + m))
  skipTel ds g i with (splitFin ds i)
    | Left  j = pure $ V (tackFinL j)  -- this should keep pointing into the telescope
    | Right j = rename (tackFinR ds) <$> g j  -- this should be modified

  export
  varDefVars : Traversal (VarDef q m) (VarDef q n) (Fin m) (TT q n)
  varDefVars g (VD n q ty) = VD n q <$> ttVars g ty

  telescopeVars' : Applicative t
    => (Fin m -> t (TT q n))
    -> Telescope q m s
    -> (t (Telescope q n s), Fin (s + m) -> t (TT q (s + n)))
  telescopeVars' g [] = (pure [], g)
  telescopeVars' g (d :: ds) with (telescopeVars' g ds)
    | (ds', g') = ((::) <$> varDefVars g' d <*> ds', skipFZ g')

  export
  telescopeVars : Traversal (Telescope q m s) (Telescope q n s) (Fin m) (TT q n)
  telescopeVars g ds = fst $ telescopeVars' g ds

  finAssoc : Fin (s + pn + m) -> Fin (s + (pn + m))
  finAssoc = replace (sym $ plusAssociative _ _ _)

  ttAssoc : TT q (s + (pn + m)) -> TT q (s + pn + m)
  ttAssoc = replace (plusAssociative _ _ _)

  export
  altVars : Traversal (Alt q m pn) (Alt q n pn) (Fin (pn + m)) (TT q (pn + n))
  altVars g (DefaultCase ct) = DefaultCase <$> caseTreeVars g ct
  altVars g (CtorCase cn args ct) = CtorCase cn
    <$> telescopeVars g args
    <*> caseTreeVars
          (map ttAssoc . skipTel args g . finAssoc)
          ct

  export
  -- this signature can't be expressed as Traversal because then (.) in altVars goes haywire
  caseTreeVars : Applicative t => (Fin (pn + m) -> t (TT q (pn + n))) -> CaseTree q m pn -> t (CaseTree q n pn)
  caseTreeVars g (Leaf tm) = Leaf <$> ttVars g tm
  caseTreeVars g (Case s alts) = Case s <$> assert_total (traverse (altVars g) alts)

  export
  ttVars : Traversal (TT q m) (TT q n) (Fin m) (TT q n)
  ttVars g (V i) = g i
  ttVars g (Lam d rhs) = Lam <$> varDefVars g d <*> ttVars (skipFZ g) rhs
  ttVars g (Pi  d rhs) = Pi  <$> varDefVars g d <*> ttVars (skipFZ g) rhs
  ttVars g (Let d val rhs) =
    Let
      <$> varDefVars g d
      <*> ttVars (skipFZ g) val
      <*> ttVars (skipFZ g) rhs
  ttVars g (App q f x)
    = App q <$> ttVars g f <*> ttVars g x
  ttVars g (Match ss pvs ct) with (telescopeVars' g pvs)
    | (pvs', g') = Match
        <$> assert_total (traverse (ttVars g) ss)
        <*> pvs'
        <*> caseTreeVars g' ct
  ttVars g Star = pure Star
  ttVars g Erased = pure Erased

  export
  subst : (Fin n -> TT q m) -> TT q n -> TT q m
  subst g = assert_total $ runIdentity . ttVars (pure . g)

  export
  rename : (Fin n -> Fin m) -> TT q n -> TT q m
  rename g = subst (V . g)

export
fold : Monoid a => (Fin n -> a) -> TT q n -> a
fold {n} f = runConst . ttVars {n} (MkConst . f)
