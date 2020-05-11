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
  pretty () (MkE Certain tc lhs rhs) =
    pretty (getCtx {q=Maybe Q} tc) lhs <++> text "=" <++> pretty (getCtx {q=Maybe Q} tc) rhs
  pretty () (MkE Uncertain tc lhs rhs) =
    pretty (getCtx {q=Maybe Q} tc) lhs <++> text "=?" <++> pretty (getCtx {q=Maybe Q} tc) rhs
