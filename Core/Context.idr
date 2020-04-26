module Core.Context

import public Core.TT
import public Core.TT.Lens
import Control.Monad.Identity

%default total

public export
Context : Type -> Nat -> Type
Context q n = Telescope q Z n

renameB : (Fin n -> Fin m) -> Binding q n -> Binding q m
renameB f = runIdentity . bindingVars (pure . V . f)

export
lookup : Fin n -> Context q n -> Binding q n
lookup  FZ    (b ::  _ ) =
  rewrite sym $ plusZeroRightNeutral n
    in renameB FS b
lookup (FS k) (_ :: ctx) = renameB FS $ lookup k ctx

{-
export
(++) : Telescope q n s -> Context q n -> Context q (s + n)
(++) [] ys = ys
(++) (b :: xs) ys = b :: xs ++ ys
-}
