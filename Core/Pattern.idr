module Core.Pattern

import public Core.TT
import public Core.TT.Lens
import public Core.TT.Pretty
import Core.TT.Utils

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
    parens $ concat $
      pretty () ctor
        :: map (\(q, arg) => text (showApp q) <+> pretty ctx arg) args
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

export
patToTm : Pat q n -> TT q n
patToTm (PV i) = V i
patToTm (PCtorApp (Forced cn) args) =
  mkApp (P cn) [(q, patToTm arg) | (q, arg) <- args]
patToTm (PCtorApp (Checked cn) args) =
  mkApp (P cn) [(q, patToTm arg) | (q, arg) <- args]
patToTm (PForced tm) = tm

export
showPat : ShowQ q => Context q n -> Pat q n -> String
showPat ctx = render "  " . pretty ctx
