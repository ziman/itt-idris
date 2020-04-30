module Core.Clause

import public Core.TT
import public Core.TT.Lens
import public Core.TT.Pretty
import public Core.Context
import public Core.Pattern

import Data.List
import Data.Vect

%default total
%undotted_record_projections off

public export
record Clause (q : Type) (argn : Nat) where
  constructor MkClause
  {pn : Nat}
  pi : Context q pn
  lhs : Vect argn (q, Pat q pn)
  rhs : TT q pn

prettyPi : ShowQ q => Context q n -> Doc -> Doc
prettyPi [] clause = clause
prettyPi pi clause =
  text "forall" <++> pretty () pi <+> text "."
    $$ indent clause

export
ShowQ q => Pretty Name (Clause q argn) where
  pretty fn c =
    prettyPi c.pi $
      pretty () fn
      <++> pretty c.pi (PCtorApp (Forced fn) (toList c.lhs))
      <++> text "~>"
      <++> pretty (PTT True NoParens, c.pi) c.rhs

export
clauseQ : Traversal (Clause q argn) (Clause q' argn) q q'
clauseQ f (MkClause pi lhs rhs) =
  [| MkClause (contextQ f pi) (traverse (qpatQ f) lhs) (ttQ f rhs) |]
