module Core.Context

import public Core.TT
import public Core.TT.Lens
import Control.Monad.Identity

%default total

public export
data Context : Type -> Nat -> Type where
  Nil : Context q Z
  (::) : Binding q n -> Context q n -> Context q (S n)

renameB : (Fin n -> Fin m) -> Binding q n -> Binding q m
renameB f = runIdentity . bindingVars (pure . V . f)

export
lookup : Fin n -> Context q n -> Binding q n
lookup  FZ    (b ::  _ ) = renameB FS b
lookup (FS k) (_ :: ctx) = renameB FS $ lookup k ctx

export
contextQ : Traversal (Context q n) (Context q' n) q q'
contextQ f Nil = pure Nil
contextQ f (b :: bs) = [| bindingQ f b :: contextQ f bs |]
