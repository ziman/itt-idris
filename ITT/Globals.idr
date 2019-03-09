module ITT.Globals

import public ITT.Core
import public Utils.Pretty
import ITT.Pretty
import Data.SortedMap

public export
data Body : (q : Type) -> Type where
  Abstract : Body q     -- postulates, primitives, ..., not a value
  Constructor : Body q  -- is a value
  Term : TT q Z -> Body q

public export
record Def (q : Type) where
  constructor D
  dn  : Name
  dq  : q
  dty : TT q Z
  db  : Body q

export
Globals : (q : Type) -> Type
Globals q = SortedMap Name (Def q)

export
lookup : Name -> Globals q -> Maybe (Def q)
lookup = SortedMap.lookup

export
ShowQ q => Pretty () (Def q) where
  pretty () (D n q ty (Term tm)) =
    text "function"
    <++> text (show n)
    <++> text ":"
    <++> pretty (PTT False NoParens, Context.Nil) ty
    <++> text "="
    <++> pretty (PTT False NoParens, Context.Nil) tm
  pretty () (D n q ty Constructor) =
    text "constructor"
    <++> text (show n)
    <++> text ":"
    <++> pretty (PTT False NoParens, Context.Nil) ty
  pretty () (D n q ty Abstract) =
    text "postulate"
    <++> text (show n)
    <++> text ":"
    <++> pretty (PTT False NoParens, Context.Nil) ty

export
ShowQ q => Show (Def q) where
  show = render "  " . pretty ()
