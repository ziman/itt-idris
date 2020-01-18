module ITT.Core.Lens

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
  bindingQ : Traversal (Binding q n) (Binding q' n) q q'
  bindingQ g (B n q ty) = B n <$> g q <*> ttQ g ty

  export
  telescopeQ : Traversal (Telescope q b s) (Telescope q' b s) q q'
  telescopeQ g [] = pure []
  telescopeQ g (b :: ds) = (::) <$> bindingQ g b <*> telescopeQ g ds

  export
  ttQ : Traversal (TT q n) (TT q' n) q q'
  ttQ g (V i) = pure $ V i
  ttQ g (Lam b rhs) = Lam <$> bindingQ g b <*> ttQ g rhs
  ttQ g (Pi  b rhs) = Pi  <$> bindingQ g b <*> ttQ g rhs
  ttQ g (App q f x) = App <$> g q <*> ttQ g f <*> ttQ g x
  ttQ g Star = pure Star
  ttQ g Erased = pure Erased
  ttQ g Bool_ = pure Bool_
  ttQ g (If_ c t e) = If_ <$> ttQ g c <*> ttQ g t <*> ttQ g e
  ttQ g True_ = pure True_
  ttQ g False_ = pure False_

mutual
  -- split references between those that point into the telescope
  -- and those that point beyond it
  export
  splitFin : Telescope q n' s -> Fin (s + n) -> Either (Fin s) (Fin n)
  splitFin [] f = Right f
  splitFin (b :: ds) f = subSplit b ds f
    where
      -- I had to break pattern matching into two separate functions
      -- because the pattern compiler kept choosing erased variables for inspection
      subSplit : Binding q (s + n') -> Telescope q n' s -> Fin (S s + n) -> Either (Fin (S s)) (Fin n)
      subSplit b ds  FZ    = Left FZ
      subSplit b ds (FS i) with (splitFin ds i)
        | Left  j = Left (FS j)
        | Right j = Right j

  -- push all references to point beyond the telescope
  export
  tackFinR : Telescope q n' s -> Fin n -> Fin (s + n)
  tackFinR []        f = f
  tackFinR (b :: ds) f = FS $ tackFinR ds f

  -- repeated weakening, identity at runtime
  export
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
  bindingVars : Traversal (Binding q m) (Binding q n) (Fin m) (TT q n)
  bindingVars g (B n q ty) = B n q <$> ttVars g ty

  telescopeVars' : Applicative t
    => (Fin m -> t (TT q n))
    -> Telescope q m s
    -> (t (Telescope q n s), Fin (s + m) -> t (TT q (s + n)))
  telescopeVars' g [] = (pure [], g)
  telescopeVars' g (b :: ds) with (telescopeVars' g ds)
    | (ds', g') = ((::) <$> bindingVars g' b <*> ds', skipFZ g')

  export
  telescopeVars : Traversal (Telescope q m s) (Telescope q n s) (Fin m) (TT q n)
  telescopeVars g ds = fst $ telescopeVars' g ds

  finAssoc : Fin (s + pn + m) -> Fin (s + (pn + m))
  finAssoc = replace (sym $ plusAssociative _ _ _)

  ttAssoc : TT q (s + (pn + m)) -> TT q (s + pn + m)
  ttAssoc = replace (plusAssociative _ _ _)

  export
  ttVars : Traversal (TT q m) (TT q n) (Fin m) (TT q n)
  ttVars g (V i) = g i
  ttVars g (Lam b rhs) = Lam <$> bindingVars g b <*> ttVars (skipFZ g) rhs
  ttVars g (Pi  b rhs) = Pi  <$> bindingVars g b <*> ttVars (skipFZ g) rhs
  ttVars g (App q f x)
    = App q <$> ttVars g f <*> ttVars g x
  ttVars g Star = pure Star
  ttVars g Erased = pure Erased
  ttVars g Bool_ = pure Bool_
  ttVars g (If_ c t e) = If_ <$> ttVars g c <*> ttVars g t <*> ttVars g e
  ttVars g True_ = pure True_
  ttVars g False_ = pure False_

  export
  subst : (Fin n -> TT q m) -> TT q n -> TT q m
  subst g = assert_total $ runIdentity . ttVars (pure . g)

  export
  rename : (Fin n -> Fin m) -> TT q n -> TT q m
  rename g = subst (V . g)

export
fold : Monoid a => (Fin n -> a) -> TT q n -> a
fold {n} f = runConst . ttVars {n} (MkConst . f)

export
weakenClosed : TT q Z -> TT q n
weakenClosed = rename tackFinL

export
substTop : Telescope q n pn -> Vect pn (TT q n) -> TT q (pn + n) -> TT q n
substTop pvs ss = runIdentity . ttVars (pure . g pvs ss)
  where
    g : Telescope q n pn -> Vect pn (TT q n)
      -> Fin (pn + n) -> TT q n
    g pvs ss i with (splitFin pvs i)
      | Left j = index j ss
      | Right j = V j
