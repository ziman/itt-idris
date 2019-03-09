module ITT.Context

import public ITT.Core
import public ITT.Lens
import Control.Monad.Identity

%default total

public export
data Context : (q : Type) -> (n : Nat) -> Type where
  Nil : Context q Z
  (::) : Binding q n -> Context q n -> Context q (S n)

export
renameB : (Fin n -> Fin m) -> Binding q n -> Binding q m
renameB f = runIdentity . bindingVars (pure . V . f)

export
lookup : Fin n -> Context q n -> Binding q n
lookup  FZ    (b ::  _ ) = renameB FS b
lookup (FS k) (_ :: ctx) = renameB FS $ lookup k ctx

export
(++) : Telescope q n s -> Context q n -> Context q (s + n)
(++) [] ys = ys
(++) (b :: xs) ys = b :: xs ++ ys
