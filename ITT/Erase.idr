module ITT.Erase

import public ITT.Core
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
erase ctx (V i) = case eraseVar ctx i of
  Nothing => Erased  -- should be unreachable if erasure's correct
  Just j => V j
erase ctx (Lam b@(B n I ty) rhs) = erase (b::ctx) rhs
erase ctx (Lam b@(B n E ty) rhs) = erase (b::ctx) rhs
erase ctx (Lam b@(B n L ty) rhs) = Lam (B n () Erased) $ erase (b::ctx) rhs
erase ctx (Lam b@(B n R ty) rhs) = Lam (B n () Erased) $ erase (b::ctx) rhs
erase ctx (Pi b@(B n I ty) rhs) = erase (b::ctx) rhs
erase ctx (Pi b@(B n E ty) rhs) = erase (b::ctx) rhs
erase ctx (Pi b@(B n L ty) rhs) = Pi (B n () Erased) $ erase (b::ctx) rhs
erase ctx (Pi b@(B n R ty) rhs) = Pi (B n () Erased) $ erase (b::ctx) rhs
erase ctx (App I f x) = erase ctx f
erase ctx (App E f x) = erase ctx f
erase ctx (App L f x) = App () (erase ctx f) (erase ctx x)
erase ctx (App R f x) = App () (erase ctx f) (erase ctx x)
erase ctx Star = Star
erase ctx Erased = Erased
erase ctx Bool_ = Bool_
erase ctx (If_ c t e) = If_ (erase ctx c) (erase ctx t) (erase ctx e)
erase ctx True_ = True_
erase ctx False_ = False_
