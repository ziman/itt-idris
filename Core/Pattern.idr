module Core.Pattern

import public Core.TT

%default total
%undotted_record_projections off

public export
data PCtor = Forced Name | Checked Name

public export
data Pat : (q : Type) -> (n : Nat) -> Type where
  PV : (pv : Fin n) -> Pat q n
  PCtorApp : PCtor -> List (q, Pat q n) -> Pat q n
  PForced : TT q n -> Pat q n
