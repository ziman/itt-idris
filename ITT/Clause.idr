module ITT.Clause

import public ITT.Core
import public ITT.Lens
import Control.Monad.Identity

%default total

public export
data Pat : (q : Type) -> (n : Nat) -> (pn : Nat) -> Type where
  PV : (i : Fin pn) -> Pat q n pn
  PCtor : (c : Name) -> Pat q n pn
  PForced : (tm : TT q (pn + n)) -> Pat q n pn
  PApp : q -> (f : Pat q n pn) -> (x : Pat q n pn) -> Pat q n pn

public export
record Lhs (q : Type) (n : Nat) (pn : Nat) where
  constructor L
  args : List (Pat q n pn)

public export
record Clause (q : Type) (n : Nat) (pn : Nat) where
  constructor C
  lhs : Lhs q n pn
  rhs : TT q (pn + n)

namespace Lens
  patTermVars : Telescope q n pn
    -> Traversal (Pat q m pn) (Pat q n pn) (Fin m) (TT q (pn + n))
  patTermVars pvs g (PV i) = pure $ PV i
  patTermVars pvs g (PCtor n) = pure $ PCtor n
  patTermVars pvs g (PApp q f x) =
    PApp q <$> patTermVars pvs g f <*> patTermVars pvs g x
  patTermVars pvs g (PForced tm) = PForced <$> ttVars (adapt pvs g) tm
    where
      adapt : Applicative f
        => Telescope q n pn
        -> (g : Fin m -> f (TT q (pn + n)))
        -> Fin (pn + m) -> f (TT q (pn + n))
      adapt pvs g i with (splitFin pvs i)
        | Left j = pure $ V (tackFinL j)
        | Right j = g j

  patPatVars : Telescope q n pn
    -> Traversal (Pat q n pn) (Pat q n pn) (Fin pn) (TT q (pn + n))
  patPatVars pvs g (PV i) = PForced <$> g i
  patPatVars pvs g (PCtor n) = pure $ PCtor n
  patPatVars pvs g (PApp q f x) =
    PApp q <$> patPatVars pvs g f <*> patPatVars pvs g x
  patPatVars pvs g (PForced tm) = PForced <$> ttVars (adapt pvs g) tm
    where
      adapt : Applicative f
        => Telescope q n pn
        -> (g : Fin pn -> f (TT q (pn + n)))
        -> Fin (pn + n) -> f (TT q (pn + n))
      adapt pvs g i with (splitFin pvs i)
        | Left j = g j
        | Right _ = pure $ V i

mkArgs : Telescope q n pn -> List (Fin pn)
mkArgs [] = []
mkArgs (b :: ds) = FZ :: map FS (mkArgs ds)


substPat : Telescope q n pn
    -> Fin pn -> TT q (pn + n)
    -> Pat q n pn -> Pat q n pn
substPat {q} {n} {pn} pvs pv tm =
    runIdentity . patPatVars pvs ?g
  where
    g : Fin pn -> Identity (TT q (pn + n))
    g i with (i == pv)
      | True  = pure tm
      | False = pure $ V (tackFinL i)

substLhs : Telescope q n pn -> Fin pn -> TT q (pn + n) -> Lhs q n pn -> Lhs q n pn
substLhs pvs i tm (L args) = L $ map (substPat pvs i tm) args

foldTree :
    (pvs : Telescope q n pn)
    -> (lhs : Lhs q n pn)
    -> (ct : CaseTree q n pn)
    -> List (Clause q n pn)
foldTree pvs lhs (Leaf rhs) = [C lhs rhs]
foldTree pvs lhs (Forced s tm ct) = foldTree pvs (substLhs pvs s tm lhs) ct
foldTree pvs lhs (Case s alts) = ?rhsC

export
foldMatch :
    (pvs : Telescope q n pn)
    -> (ss : Vect pn (TT q n))
    -> (ty : TT q (pn + n))
    -> (ct : CaseTree q n pn)
    -> List (Clause q n pn)
foldMatch {q} {n} {pn} pvs ss ty ct
    = foldTree pvs lhs ct
  where
    lhs : Lhs q n pn
    lhs = L $ map PV $ mkArgs pvs
