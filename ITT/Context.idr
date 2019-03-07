module ITT.Context

import public ITT.Core
import ITT.Lens

%default total

public export
Context : Type -> Nat -> Type
Context = Telescope q Z n

export
lookupCtx : Fin n -> Context q n -> Def q n
lookupCtx  FZ    (d ::  _ ) = renameDef FS d
lookupCtx (FS k) (_ :: ctx) = renameDef FS $ lookupCtx k ctx
