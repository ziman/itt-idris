module Core.Erase

import public Core.TT
import public Core.Context
import public Core.Pattern
import public Core.Globals
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

-- eraseTm for runtime
export
eraseTm : (ctx : Context Q n) -> (tm : TT Q n) -> TT () (eraseN ctx)
eraseTm ctx (P n) = P n
eraseTm ctx (V i) = case eraseVar ctx i of
  Nothing => Erased  -- should be unreachable if erasure's correct
  Just j => V j
eraseTm ctx (Lam (B n I ty) rhs) = eraseTm (B n I ty::ctx) rhs
eraseTm ctx (Lam (B n E ty) rhs) = eraseTm (B n E ty::ctx) rhs
eraseTm ctx (Lam (B n L ty) rhs) = Lam (B n () Erased) $ eraseTm (B n L ty::ctx) rhs
eraseTm ctx (Lam (B n R ty) rhs) = Lam (B n () Erased) $ eraseTm (B n R ty::ctx) rhs
eraseTm ctx (Pi (B n I ty) rhs) = eraseTm (B n I ty::ctx) rhs
eraseTm ctx (Pi (B n E ty) rhs) = eraseTm (B n E ty::ctx) rhs
eraseTm ctx (Pi (B n L ty) rhs) = Pi (B n () Erased) $ eraseTm (B n L ty::ctx) rhs
eraseTm ctx (Pi (B n R ty) rhs) = Pi (B n () Erased) $ eraseTm (B n R ty::ctx) rhs
eraseTm ctx (App I f x) = eraseTm ctx f
eraseTm ctx (App E f x) = eraseTm ctx f
eraseTm ctx (App L f x) = App () (eraseTm ctx f) (eraseTm ctx x)
eraseTm ctx (App R f x) = App () (eraseTm ctx f) (eraseTm ctx x)
eraseTm ctx Type_ = Type_
eraseTm ctx Erased = Erased

mutual
  eraseArgs : (ctx : Context Q n) -> List (Q, Pat Q n) -> List ((), Pat () (eraseN ctx))
  eraseArgs ctx [] = []
  eraseArgs ctx ((I, _) :: args) = eraseArgs ctx args
  eraseArgs ctx ((E, _) :: args) = eraseArgs ctx args
  eraseArgs ctx ((L, arg) :: args) = ((), erasePat ctx arg) :: eraseArgs ctx args
  eraseArgs ctx ((R, arg) :: args) = ((), erasePat ctx arg) :: eraseArgs ctx args

  erasePat : (ctx : Context Q n) -> (pat : Pat Q n) -> Pat () (eraseN ctx)
  erasePat ctx (PV i) =
    case eraseVar ctx i of
      Nothing => PWildcard
      Just j => PV j
  erasePat ctx (PCtorApp ctor args) = PCtorApp ctor $ eraseArgs ctx args
  erasePat ctx (PForced tm) = PForced $ eraseTm ctx tm
  erasePat ctx PWildcard = PWildcard

eraseCtx : (ctx : Context Q n) -> Context () (eraseN ctx)
eraseCtx [] = []
eraseCtx (B n I ty :: ds) = eraseCtx ds
eraseCtx (B n E ty :: ds) = eraseCtx ds
eraseCtx (B n L ty :: ds) = B n () Erased :: eraseCtx ds
eraseCtx (B n R ty :: ds) = B n () Erased :: eraseCtx ds

eraseClause : Clause Q argn -> RawClause ()
eraseClause (MkClause pi lhs rhs) =
  MkRC
    (eraseCtx pi)
    (eraseArgs pi $ toList lhs)
    (eraseTm pi rhs)

eraseBody : Binding Q Z -> Body Q -> Body ()
eraseBody b Postulate = Postulate
eraseBody b (Constructor arity) =
  Constructor $ piDepth (eraseTm [] b.type)
eraseBody b (Foreign code) = Foreign code
eraseBody b (Clauses argn cs) =
  case fromRaw $ map eraseClause cs of
    Nothing => Clauses Z []  -- should never happen
    Just (argn' ** cs) => Clauses argn' cs

eraseDefs : List (Definition Q) -> List (Definition ())
eraseDefs [] = []
eraseDefs ((MkDef b@(B n q ty) body) :: ds) =
  case q of
    I => eraseDefs ds
    E => eraseDefs ds
    _ =>
        MkDef
          (B n () Erased)
          (eraseBody b body)
        :: eraseDefs ds

export
eraseGlobals : (gs : Globals Q) -> Globals ()
eraseGlobals = fromBlocks . map eraseDefs . toBlocks
