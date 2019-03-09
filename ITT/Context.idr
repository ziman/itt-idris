module ITT.Context

import public ITT.Core
import public ITT.Lens
import Control.Monad.Identity

%default total

public export
Context : (q : Type) -> (n : Nat) -> Type
Context q n = Telescope q Z n

export
renameB : (Fin n -> Fin m) -> Binding q n -> Binding q m
renameB f = runIdentity . bindingVars (pure . V . f)

export
lookup : Fin n -> Context q n -> Binding q n
lookup  FZ    (b ::  _ ) = replace (plusZeroRightNeutral _) $ renameB FS b
lookup (FS k) (_ :: ctx) = renameB FS $ lookup k ctx
