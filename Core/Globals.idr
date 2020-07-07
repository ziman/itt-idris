module Core.Globals

import public Core.TT
import public Core.TT.Lens
import public Core.TT.Pretty
import public Core.Clause
import Data.List
import Data.SortedMap

%default total

public export
data Body : (q : Type) -> Type where
  Postulate : Body q
  Constructor : (arity : Nat) -> Body q
  Foreign : String -> Body q
  Clauses : (argn : Nat) -> List (Clause q argn) -> Body q

export
ShowQ q => Pretty Name (Body q) where
  pretty n Postulate = text "postulate"
  pretty n (Constructor arity) = text "constructor/" <+> show arity
  pretty n (Foreign code) = text "foreign" <++> text (show code)
  pretty n (Clauses argn cs) = vcat (map (pretty n) cs)

public export
record Definition (q : Type) where
  constructor MkDef
  binding : Binding q Z
  body : Body q

export
ShowQ q => Pretty () (Definition q) where
  pretty () (MkDef b Postulate) =
    text "postulate" <++> pretty (Context.Nil {q}) b <+> text "."

  pretty () (MkDef b (Constructor arity)) =
    text "constructor/" <+> show arity
        <++> pretty (Context.Nil {q}) b <+> text "."

  pretty () (MkDef b (Foreign code)) =
    text "foreign" <++> pretty (Context.Nil {q}) b
        $$ indent (text "=" <++> text (show code) <+> text ".")

  pretty () (MkDef b (Clauses argn cs)) =
    pretty (Context.Nil {q}) b <++> text "{"
    $$ indent (vcat (intersperse (text "") $ map (pretty (UN b.name)) cs))
    $$ text "}"

export
record Globals (q : Type) where
  constructor MkGlobals
  definitions : SortedMap Name (Definition q)

  -- list of mutual blocks
  -- the outer list is stored reversed for fast append!
  -- the inner list is _not_ reversed, however
  ordering : List (List Name)

export
empty : Globals q
empty = MkGlobals empty []

export
lookup : Name -> Globals q -> Maybe (Definition q)
lookup n gs = lookup n gs.definitions

export
map : (Definition q -> Definition q') -> Globals q -> Globals q'
map f (MkGlobals ds ord) = MkGlobals (f <$> ds) ord

export
snoc : Globals q -> Definition q -> Globals q
snoc (MkGlobals ds ord) d =
  let n = UN d.binding.name
    in MkGlobals (insert n d ds) ([n] :: ord)

export
snocBlock : Globals q -> List (Definition q) -> Globals q
snocBlock gs [] = gs
snocBlock (MkGlobals ds ord) dsBlk =
  let ns = map (UN . name . binding) dsBlk
      dsBlkMap = SortedMap.fromList [(UN d.binding.name, d) | d <- dsBlk]
   in MkGlobals (ds `mergeLeft` dsBlkMap) (ns :: ord)

export
toBlocks : Globals q -> List (List (Definition q))
toBlocks gs with (gs.ordering)
  toBlocks gs | nss with (Prelude.Nil {a = List $ Definition q})
    toBlocks gs |        [] | acc = acc
    toBlocks gs | ns :: nss | acc =
      case sequence [lookup n gs | n <- ns] of
        Nothing => toBlocks gs | nss |       acc
        Just ds => toBlocks gs | nss | ds :: acc

export
fromBlocks : List (List (Definition q)) -> Globals q
fromBlocks = foldl snocBlock empty

export
ShowQ q => Pretty () (List (Definition q)) where
  pretty () [d] = pretty () d
  pretty () ds =
    text "mutual {"
    $$ indentBlock (intersperse (text "") [pretty () d | d <- ds])
    $$ text "}"

export
ShowQ q => Pretty () (Globals q) where
  pretty () gs = vsep [pretty () blk | blk <- toBlocks gs]

export
ShowQ q => Show (Globals q) where
  show = render "  " . pretty ()

export
bodyQ : Traversal (Body q) (Body q') q q'
bodyQ f Postulate = pure Postulate
bodyQ f (Constructor arity) = pure (Constructor arity)
bodyQ f (Foreign code) = pure $ Foreign code
bodyQ f (Clauses argn cs) = Clauses argn <$> traverse (clauseQ f) cs

export
definitionQ : Traversal (Definition q) (Definition q') q q'
definitionQ f (MkDef binding body) = MkDef <$> bindingQ f binding <*> bodyQ f body

export
globalsQ : Traversal (Globals q) (Globals q') q q'
globalsQ f (MkGlobals ds ord) =
  MkGlobals
    <$> traverse (definitionQ f) ds
    <*> pure ord
