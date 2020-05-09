module Transformation.DefaultCtorQuantities

import Core.TT
import Core.TT.Utils
import public Core.Globals

byDefault : Q -> TT (Maybe Q) n -> TT (Maybe Q) n
byDefault q (Pi (B n Nothing ty) rhs) = Pi (B n (Just q) ty) $ byDefault q rhs
byDefault q (Pi b rhs) = Pi b $ byDefault q rhs
byDefault q tm = tm

fixup : Definition (Maybe Q) -> Definition (Maybe Q)
fixup (MkDef (B n q ty) (Constructor arity)) =
  MkDef (B n q (byDefault L ty)) (Constructor arity)
fixup d = d

public export
applyDefaultCtorQuantities : Globals (Maybe Q) -> Globals (Maybe Q)
applyDefaultCtorQuantities = map fixup
