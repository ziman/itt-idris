module Elab.Equality

import public Core.Context
import public Core.Quantity
import public Core.TT

import Core.TC
import Core.TT.Pretty

%default total
%undotted_record_projections off

public export
data Certainty = Certain | Uncertain

export
symbol : Certainty -> Doc
symbol Certain = text "="
symbol Uncertain = text "=?"

export
Semigroup Certainty where
  Certain <+> Certain = Certain
  _ <+> _ = Uncertain

public export
record Equality where
  constructor MkE
  {n : Nat}
  certainty : Certainty
  tc : Suspended (Maybe Q) n
  lhs : TT (Maybe Q) n
  rhs : TT (Maybe Q) n

export
Pretty () Equality where
  pretty () (MkE c tc lhs rhs) =
    pretty (getCtx {q=Maybe Q} tc) lhs <++> symbol c <++> pretty (getCtx {q=Maybe Q} tc) rhs
