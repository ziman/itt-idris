module ITT.Clause

import ITT.Core

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

mkArgs : Telescope q n pn -> List (Fin pn)
mkArgs [] = []
mkArgs (b :: ds) = FZ :: map FS (mkArgs ds)

substPat : Fin pn -> TT q (pn + n) -> Pat q n pn -> Pat q n pn
substPat i tm pat = ?rhsP

substLhs : Fin pn -> TT q (pn + n) -> Lhs q n pn -> Lhs q n pn
substLhs i tm (L args) = L $ map (substPat i tm) args

foldTree : (lhs : Lhs q n pn)
    -> (ct : CaseTree q n pn)
    -> List (Clause q n pn)
foldTree lhs (Leaf rhs) = [C lhs rhs]
foldTree lhs (Forced s tm ct) = foldTree (substLhs s tm lhs) ct
foldTree lhs (Case s alts) = ?rhsC

export
foldMatch :
    (pvs : Telescope q n pn)
    -> (ss : Vect pn (TT q n))
    -> (ty : TT q (pn + n))
    -> (ct : CaseTree q n pn)
    -> List (Clause q n pn)
foldMatch {q} {n} {pn} pvs ss ty ct
    = foldTree lhs ct
  where
    lhs : Lhs q n pn
    lhs = L $ map PV $ mkArgs pvs
