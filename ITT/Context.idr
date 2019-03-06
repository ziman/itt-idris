module ITT.Context

import public ITT.Core
import ITT.Lens

public export
data Context : Type -> Nat -> Type where
  Nil : Context q Z
  (::) : Def q n -> Context q n -> Context q (S n)

export
lookupCtx : Fin n -> Context q n -> Def q n
lookupCtx  FZ    (d ::  _ ) = renameDef FS d
lookupCtx (FS k) (_ :: ctx) = renameDef FS $ lookupCtx k ctx
