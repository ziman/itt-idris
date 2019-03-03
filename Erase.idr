module Erase

import TT
import Data.List

eraseN : Context Q n -> Nat
eraseN [] = Z
eraseN (D n I ty :: ds) = eraseN ds
eraseN (D n E ty :: ds) = eraseN ds
eraseN (D n L ty :: ds) = S (eraseN ds)
eraseN (D n R ty :: ds) = S (eraseN ds)

eraseVar : (ctx : Context Q n) -> Fin n -> Maybe (Fin (eraseN ctx))
eraseVar (D n I ty :: ds) FZ = Nothing
eraseVar (D n E ty :: ds) FZ = Nothing
eraseVar (D n L ty :: ds) FZ = Just FZ
eraseVar (D n R ty :: ds) FZ = Just FZ
eraseVar (D n q ty :: ds) (FS i) with (eraseVar ds i)
  eraseVar (D n I ty :: ds) (FS i) | ev = ev
  eraseVar (D n E ty :: ds) (FS i) | ev = ev
  eraseVar (D n L ty :: ds) (FS i) | ev = FS <$> ev
  eraseVar (D n R ty :: ds) (FS i) | ev = FS <$> ev

-- erase for runtime
erase : (ctx : Context Q n) -> (tm : TT Q n) -> TT () (eraseN ctx)
erase ctx (V i) with (eraseVar ctx i)
  | Nothing = Erased  -- should be unreachable if erasure's correct
  | Just j = V j
erase ctx (Bind b d@(D n I ty) rhs) = erase (d::ctx) rhs
erase ctx (Bind b d@(D n E ty) rhs) = erase (d::ctx) rhs
erase ctx (Bind b d@(D n L ty) rhs) = Bind b (D n () Erased) $ erase (d::ctx) rhs
erase ctx (Bind b d@(D n R ty) rhs) = Bind b (D n () Erased) $ erase (d::ctx) rhs
erase ctx (App I f x) = erase ctx f
erase ctx (App E f x) = erase ctx f
erase ctx (App L f x) = App () (erase ctx f) (erase ctx x)
erase ctx (App R f x) = App () (erase ctx f) (erase ctx x)
erase ctx Star = Star
