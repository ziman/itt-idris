module Transformation.DefaultCtorQuantities

import Core.TT
import Core.TT.Utils
import public Core.Globals

fixupTy : TT (Maybe Q) n -> TT (Maybe Q) n

-- meta-typed args (usually introduced by forall) are I by default
fixupTy (Pi (B n Nothing ty@(Meta _)) rhs) = Pi (B n (Just I) ty) $ fixupTy rhs

-- other constructor args are L by default
fixupTy (Pi (B n Nothing ty) rhs) = Pi (B n (Just L) ty) $ fixupTy rhs

-- don't touch args with explicit quantities
fixupTy (Pi b rhs) = Pi b $ fixupTy rhs

-- not a pi
fixupTy tm = tm

fixup : Definition (Maybe Q) -> Definition (Maybe Q)
fixup (MkDef (B n q ty) (Constructor arity)) =
  MkDef (B n q (fixupTy ty)) (Constructor arity)
fixup d = d

public export
applyDefaultCtorQuantities : Globals (Maybe Q) -> Globals (Maybe Q)
applyDefaultCtorQuantities = map fixup
