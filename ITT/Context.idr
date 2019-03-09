module ITT.Context

import public ITT.Core
import public ITT.Lens
import Control.Monad.Identity

%default total

public export
data Body : (q : Type) -> (n : Nat) -> Type where
  Variable : Body q n
  Constructor : Body q n
  Term : TT q n -> Body q n

public export
record Def (q : Type) (n : Nat) where
  constructor D
  defName : String
  defQ    : q
  defType : TT q n
  defBody : Body q (S n)

public export
data Context : (q : Type) -> (n : Nat) -> Type where
  Nil : Context q Z
  (::) : Def q n -> Context q n -> Context q (S n)

namespace Lens
  export
  bodyQ : Traversal (Body q n) (Body q' n) q q'
  bodyQ g Variable = pure Variable
  bodyQ g Constructor = pure Constructor
  bodyQ g (Term tm) = Term <$> ttQ g tm

  export
  defQ : Traversal (Def q n) (Def q' n) q q'
  defQ g (D n q ty b) = D n <$> g q <*> ttQ g ty <*> bodyQ g b

  export
  bodyVars : Traversal (Body q m) (Body q n) (Fin m) (TT q n)
  bodyVars g Variable = pure Variable
  bodyVars g Constructor = pure Constructor
  bodyVars g (Term tm) = Term <$> ttVars g tm
  
  export
  defVars : Traversal (Def q m) (Def q n) (Fin m) (TT q n)
  defVars g (D n q ty b) = D n q <$> ttVars g ty <*> bodyVars (skipFZ g) b

export
renameInDef : (Fin n -> Fin m) -> Def q n -> Def q m
renameInDef f = runIdentity . defVars (pure . V . f)

export
lookupCtx : Fin n -> Context q n -> Def q n
lookupCtx  FZ    (d ::  _ ) = renameInDef FS d
lookupCtx (FS k) (_ :: ctx) = renameInDef FS $ lookupCtx k ctx

export
(++) : Telescope q n s -> Context q n -> Context q (s + n)
(++) [] ys = ys
(++) (AD n q ty :: xs) ys = D n q ty Variable :: xs ++ ys
