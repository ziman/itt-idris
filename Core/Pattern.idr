module Core.Pattern

import public Core.TT
import public Core.TT.Lens
import public Core.TT.Pretty

%default total
%undotted_record_projections off

public export
data PCtor = Forced Name | Checked Name

public export
data Pat : (q : Type) -> (n : Nat) -> Type where
  PV : (pv : Fin n) -> Pat q n
  PCtorApp : PCtor -> List (q, Pat q n) -> Pat q n
  PForced : TT q n -> Pat q n

export
ShowQ q => Pretty () PCtor where
  pretty () (Checked n) = pretty () n
  pretty () (Forced n) = braces (pretty () n)

export
ShowQ q => Pretty (Context q n) (Pat q n) where
  pretty ctx (PV i) = text (lookup i ctx).name
  pretty ctx (PCtorApp ctor []) = pretty () ctor
  pretty ctx (PCtorApp ctor args) =
    parens $ hsep (pretty () ctor :: map (pretty ctx . snd) args)
  pretty ctx (PForced tm) = brackets $ pretty ctx tm

mutual
  export
  qpatQ : Traversal (q, Pat q n) (q', Pat q' n) q q'
  qpatQ f (q, pat) = MkPair <$> f q <*> patQ f pat

  export
  patQ : Traversal (Pat q n) (Pat q' n) q q'
  patQ f (PV i) = pure $ PV i
  patQ f (PCtorApp cn args) = PCtorApp cn <$> traverse (qpatQ f) args
  patQ f (PForced tm) = PForced <$> ttQ f tm
