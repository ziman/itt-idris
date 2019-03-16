module ITT.Module

import public ITT.Core
import public ITT.Lens
import public Utils.Pretty
import Inference.Evar
import ITT.Pretty
import public Data.SortedMap as Map
import Data.SortedSet as Set

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
bodyQ : Traversal (Body q) (Body q') q q'
bodyQ g Abstract = pure Abstract
bodyQ g Constructor = pure Constructor
bodyQ g (Term tm) = Term <$> ttQ g tm

export
defQ : Traversal (Def q) (Def q') q q'
defQ g (D n q ty b) = D n <$> g q <*> ttQ g ty <*> bodyQ g b

public export
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
    <++> text (showCol q)
    <++> pretty (PTT False NoParens, Context.Nil) ty
    <++> text "="
    $$ indent (pretty (PTT True NoParens, Context.Nil) tm)
  pretty () (D n q ty Constructor) =
    text "constructor"
    <++> text (show n)
    <++> text (showCol q)
    <++> pretty (PTT False NoParens, Context.Nil) ty
  pretty () (D n q ty Abstract) =
    text "postulate"
    <++> text (show n)
    <++> text (showCol q)
    <++> pretty (PTT False NoParens, Context.Nil) ty

export
ShowQ q => Show (Def q) where
  show = render "  " . pretty ()

public export
record Module (q : Type) where
  constructor MkModule
  definitions : List (Def q)

export
moduleQ : Traversal (Module q) (Module q') q q'
moduleQ g (MkModule ds) = MkModule <$> traverse (defQ g) ds

export
toGlobals : Module q -> Globals q
toGlobals (MkModule ds) = Map.fromList [(dn d, d) | d <- ds]

export
ShowQ q => Pretty () (Module q) where
  pretty () (MkModule ds) = vcat $
    map (\d => pretty () d $$ text "") ds

export
ShowQ q => Show (Module q) where
  show = render "  " . pretty ()
