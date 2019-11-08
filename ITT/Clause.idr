module ITT.Clause

import public ITT.Core
import public ITT.Lens

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
  patTermVars : Traversal (Pat q m pn) (Pat q n pn) (Fin m) (TT q n)
  patTermVars g pat = ?rhs

mkArgs : Telescope q n pn -> List (Fin pn)
mkArgs [] = []
mkArgs (b :: ds) = FZ :: map FS (mkArgs ds)


substPat : Telescope q n pn
    -> Fin pn -> TT q (pn + n)
    -> Pat q n pn -> Pat q n pn
{-
substPat pvs i tm (PV j) with (i == j)
  | True  = PForced tm
  | False = PV j
substPat pvs i tm (PCtor c) = PCtor c
substPat pvs i tm (PApp q f x) = PApp q (substPat pvs i tm f) (substPat pvs i tm x)
substPat {pn} {q} {n} pvs i tm (PForced tmf) = PForced $ subst sf tmf
  where
    sf : Fin (pn + n) -> TT q (pn + n)
    sf j with (splitFin pvs j)
      | Left k with (k == i)
        | True  = tm
        | False = PV j
      | Right _ = PV j
-}

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
