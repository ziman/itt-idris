module Core.Clause

import public Core.TT
import public Core.TT.Pretty
import public Core.Context
import public Core.Pattern

import Data.List

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
      <++> hsep [pretty c.pi pat | (q, pat) <- toList c.lhs]
      <++> text "~>"
      <++> pretty (PTT True NoParens, c.pi) c.rhs
