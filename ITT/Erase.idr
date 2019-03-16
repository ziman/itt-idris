module Erase

import public ITT.Core
import public ITT.Module
import public ITT.Context
import Data.List

%default total

public export
eraseN : Context Q n -> Nat
eraseN [] = Z
eraseN (B n I ty :: ds) = eraseN ds
eraseN (B n E ty :: ds) = eraseN ds
eraseN (B n L ty :: ds) = S (eraseN ds)
eraseN (B n R ty :: ds) = S (eraseN ds)

eraseVar : (ctx : Context Q n) -> Fin n -> Maybe (Fin (eraseN ctx))
eraseVar (B n I ty :: ds) FZ = Nothing
eraseVar (B n E ty :: ds) FZ = Nothing
eraseVar (B n L ty :: ds) FZ = Just FZ
eraseVar (B n R ty :: ds) FZ = Just FZ
eraseVar (B n q ty :: ds) (FS i) with (eraseVar ds i)
  eraseVar (B n I ty :: ds) (FS i) | ev = ev
  eraseVar (B n E ty :: ds) (FS i) | ev = ev
  eraseVar (B n L ty :: ds) (FS i) | ev = FS <$> ev
  eraseVar (B n R ty :: ds) (FS i) | ev = FS <$> ev

-- erase for runtime
export
erase : (ctx : Context Q n) -> (tm : TT Q n) -> TT () (eraseN ctx)
erase ctx (V i) with (eraseVar ctx i)
  | Nothing = Erased  -- should be unreachable if erasure's correct
  | Just j = V j
erase ctx (G n) = G n
erase ctx (Lam b@(B n I ty) rhs) = erase (b::ctx) rhs
erase ctx (Lam b@(B n E ty) rhs) = erase (b::ctx) rhs
erase ctx (Lam b@(B n L ty) rhs) = Lam (B n () Erased) $ erase (b::ctx) rhs
erase ctx (Lam b@(B n R ty) rhs) = Lam (B n () Erased) $ erase (b::ctx) rhs
erase ctx (Pi b@(B n I ty) rhs) = erase (b::ctx) rhs
erase ctx (Pi b@(B n E ty) rhs) = erase (b::ctx) rhs
erase ctx (Pi b@(B n L ty) rhs) = Pi (B n () Erased) $ erase (b::ctx) rhs
erase ctx (Pi b@(B n R ty) rhs) = Pi (B n () Erased) $ erase (b::ctx) rhs
erase ctx (Let b@(B n I ty) val rhs) = erase (b::ctx) rhs
erase ctx (Let b@(B n E ty) val rhs) = erase (b::ctx) rhs
erase ctx (Let b@(B n L ty) val rhs)
    = Let (B n () Erased) (erase (b::ctx) val) (erase (b::ctx) rhs)
erase ctx (Let b@(B n R ty) val rhs)
    = Let (B n () Erased) (erase (b::ctx) val) (erase (b::ctx) rhs)
erase ctx (App I f x) = erase ctx f
erase ctx (App E f x) = erase ctx f
erase ctx (App L f x) = App () (erase ctx f) (erase ctx x)
erase ctx (App R f x) = App () (erase ctx f) (erase ctx x)
erase ctx (Match pvs ss rty ct) = Erased  -- TODO
erase ctx Star = Star
erase ctx Erased = Erased

export
eraseBody : Body Q -> Body ()
eraseBody Abstract = Abstract
eraseBody Constructor = Constructor
eraseBody (Term tm) = Term $ erase [] tm

export
eraseDefs : List (Def Q) -> List (Def ())
eraseDefs [] = []
eraseDefs (D _ I _ _ :: ds) = eraseDefs ds
eraseDefs (D _ E _ _ :: ds) = eraseDefs ds
eraseDefs (D n L ty body :: ds) =
  D n () (erase [] ty) (eraseBody body) :: eraseDefs ds
eraseDefs (D n R ty body :: ds) =
  D n () (erase [] ty) (eraseBody body) :: eraseDefs ds

export
eraseModule : Module Q -> Module ()
eraseModule (MkModule ds) = MkModule (eraseDefs ds)
