module Erase

import TT
import Data.List

{-
eraseCtx : Context Q n -> (m ** Context Q m)
eraseCtx [] = (Z ** [])
eraseCtx (D n I ty :: ds) = ?rhs_1
eraseCtx (D n E ty :: ds) = ?rhs_2
eraseCtx (D n L ty :: ds) = ?rhs_3
eraseCtx (D n R ty :: ds) = ?rhs_4
-}

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

eraseTm : (ctx : Context Q n) -> (tm : TT Q n) -> TT () (eraseN ctx)
eraseTm ctx (V i) with (eraseVar ctx i)
  | Nothing = ?rhs_1
  | Just j = V j
eraseTm ctx (Bind b d@(D n I ty) rhs) = eraseTm (d::ctx) rhs
eraseTm ctx (Bind b d@(D n E ty) rhs) = eraseTm (d::ctx) rhs
eraseTm ctx (Bind b d@(D n L ty) rhs) = Bind b (D n () $ eraseTm ctx ty) $ eraseTm (d::ctx) rhs
eraseTm ctx (Bind b d@(D n R ty) rhs) = Bind b (D n () $ eraseTm ctx ty) $ eraseTm (d::ctx) rhs
eraseTm ctx (App I f x) = eraseTm ctx f
eraseTm ctx (App E f x) = eraseTm ctx f
eraseTm ctx (App L f x) = App () (eraseTm ctx f) (eraseTm ctx x)
eraseTm ctx (App R f x) = App () (eraseTm ctx f) (eraseTm ctx x)
eraseTm ctx Star = Star

{-
mutual
  record Def (qty : Type) (qs : List qty) where
    constructor D
    defName : String
    defQ : qty
    defType : TTE qty qs

  data TTE : (qty : Type) -> List qty -> Type where
    V : (q : qty) -> Elem q qs -> TTE qty qs
    Bind : Binder -> (d : Def qty qs) -> TTE qty (defQ d :: qs) -> TTE qty qs
    App : (q : qty) -> (f, x : TTE qty qs) -> TTE qty qs
    Star : TTE qty qs

finToElem : Fin (length qs) -> (q ** Elem q qs)
finToElem {qs=[]} FZ impossible
finToElem {qs=[]} (FS _) impossible
finToElem {qs=q::qs} FZ = (q ** Here)
finToElem {qs=q::qs} (FS i) with (finToElem i)
  | (q ** elem) = (q ** There elem)

toE : (qs : List qty) -> TT qty (length qs) -> TTE qty qs
toE qs (V i) with (finToElem i)
  | (q ** elem) = V q elem
toE qs (Bind b (D n q ty) rhs) = Bind b (D n q (toE qs ty)) (toE (q :: qs) rhs)
toE qs (App q f x) = App q (toE qs f) (toE qs x)
toE qs Star = Star

eraseQs : List Q -> List ()
eraseQs [] = []
eraseQs (I :: qs) = eraseQs qs
eraseQs (E :: qs) = eraseQs qs
eraseQs (L :: qs) = () :: eraseQs qs
eraseQs (R :: qs) = () :: eraseQs qs

eraseFin : {qs : List Q} -> Fin (length qs) -> Fin (length $ eraseQs qs)
-}

{-
eraseRT : TTE Q qs -> TTE () (eraseQs qs)
eraseRT (V i) = V i
eraseRT (Bind x d y) = ?rhs_2
eraseRT (App q f x) = ?rhs_3
eraseRT Star = ?rhs_4
-}
