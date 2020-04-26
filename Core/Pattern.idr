module Core.Pattern

import public Core.TT

%default total
%undotted_record_projections off

public export
data Pat : (q : Type) -> (n : Nat) -> Type where
  PV : (pv : Fin n) -> Pat q n
  PCtor : (isForced : Bool) -> (cn : Name) -> List (q, Pat q n) -> Pat q n
  PForced : TT q n -> Pat q n
