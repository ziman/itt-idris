module Elab.Equality

import public Core.Context
import public Core.Quantity
import public Core.TT

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
  {0 n : Nat}
  certainty : Certainty
  context : Context (Maybe Q) n
  lhs : TT (Maybe Q) n
  rhs : TT (Maybe Q) n

export
Pretty () Equality where
  pretty () (MkE Certain ctx lhs rhs) =
    pretty ctx lhs <++> text "=" <++> pretty ctx rhs
  pretty () (MkE Uncertain ctx lhs rhs) =
    pretty ctx lhs <++> text "=?" <++> pretty ctx rhs
