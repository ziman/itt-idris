module Core.Pattern

import public Core.TT

%default total
%undotted_record_projections off

public export
data Pat : (q : Type) -> (n : Nat) -> Type where
  PV : (pv : Fin n) -> Pat q n
  PC : (cn : Name) -> Pat q n
  PApp : q -> Pat q n -> Pat q n -> Pat q n
  PForced : TT q n -> Pat q n
