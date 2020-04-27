module Core.Globals

import public Core.TT
import public Core.TT.Pretty
import public Core.Clause
import Data.SortedMap

%default total
%undotted_record_projections off

public export
data Body : (q : Type) -> Type where
  Postulate : Body q
  Constructor : Body q
  Foreign : String -> Body q
  Clauses : (argn : Nat) -> List (Clause q argn) -> Body q

export
ShowQ q => Pretty Name (Body q) where
  pretty n Postulate = text "postulate"
  pretty n Constructor = text "constructor"
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
    text "postulate" <++> parens (pretty (Context.Nil {q}) b)

  pretty () (MkDef b Constructor) =
    text "constructor" <++> parens (pretty (Context.Nil {q}) b)

  pretty () (MkDef b (Foreign code)) =
    text "foreign" <++> parens (pretty (Context.Nil {q}) b) <++> text "=" <++> text (show code)

  pretty () (MkDef b (Clauses argn cs)) =
    pretty (Context.Nil {q}) b <++> text "{"
    $$ indent (vcat (map (pretty (UN b.name)) cs))
    $$ text "}"

export
record Globals (q : Type) where
  constructor MkGlobals
  definitions : SortedMap Name (Definition q)

export
ShowQ q => Pretty () (Globals q) where
  pretty () gs = vcat
    [ pretty () d $$ text ""
    | (_, d) <- SortedMap.toList $ gs.definitions
    ]

export
lookup : Name -> Globals q -> Maybe (Definition q)
lookup n gs = lookup n gs.definitions

export
toGlobals : List (Definition q) -> Globals q
toGlobals ds =
  MkGlobals $ SortedMap.fromList
    [(UN d.binding.name, d) | d <- ds]
