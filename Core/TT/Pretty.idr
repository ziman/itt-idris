module Core.TT.Pretty

import public Core.TT
import public Core.Context
import public Core.Quantity
import public Utils.Pretty

%default total
%undotted_record_projections off

public export
data NestingLevel
  = NoParens
  | NoAppParens
  | UseParens

nlToInt : NestingLevel -> Int
nlToInt NoParens = 0
nlToInt NoAppParens = 1
nlToInt UseParens = 2

export
Eq NestingLevel where
  (==) = eqBy nlToInt

export
Ord NestingLevel where
  compare = compareBy nlToInt

export
Pretty () Name where
  pretty () n = text $ show n

public export
record PrettyTT where
  constructor PTT
  multiLineLam : Bool
  nestingLevel : NestingLevel

parensFrom : NestingLevel -> NestingLevel -> Doc -> Doc
parensFrom required actual =
  if actual >= required
    then parens
    else id

mutual
  export
  ShowQ q => Pretty (Context q n) (Binding q n) where
    pretty ctx (B n dq Erased)
      = text n
    pretty ctx (B n dq ty)
      = text n <++> text (showCol dq) <++> pretty (PTT False NoParens, ctx) ty

  export
  ShowQ q => Pretty (PrettyTT, Context q n) (TT q n) where
    pretty (PTT top nl, ctx) (P n) = pretty () n
    pretty (PTT top nl, ctx) (V i) = case lookup i ctx of
      B n q' ty => text n
    pretty (PTT True nl,  ctx) (Lam b rhs) = parensFrom NoAppParens nl $
      text "\\" <+> pretty ctx b <+> text "."
      $$ indent (pretty (PTT True NoParens, b::ctx) rhs)
    pretty (PTT False nl, ctx) (Lam b rhs) = parensFrom NoAppParens nl $
      text "\\" <+> pretty ctx b <+> text "."
      <++> pretty (PTT True NoParens, b::ctx) rhs
    {-
    pretty (PTT top nl, ctx) (Pi b@(B "_" q ty) rhs) = parensFrom NoAppParens nl $
      pretty (PTT False NoAppParens, ctx) ty
      <++> text "->" <++> pretty (PTT False NoParens, b::ctx) rhs
    -}
    pretty (PTT top nl, ctx) (Pi b rhs) = parensFrom NoAppParens nl $
      parens (pretty ctx b)
      <++> text "->" <++> pretty (PTT False NoParens, b::ctx) rhs
    pretty (PTT top nl, ctx) (App q' f x) = parensFrom UseParens nl $
      pretty (PTT False NoAppParens, ctx) f 
      <+> text (showApp q')
      <+> pretty (PTT False UseParens, ctx) x
    pretty (PTT top nl, ctx) Type_ = text "Type"
    pretty (PTT top nl, ctx) Erased = text "_"

export
ShowQ q => Pretty (Context q n) (TT q n) where
  pretty ctx = pretty (PTT False NoAppParens, ctx)

export
ShowQ q => Pretty () (TT q Z) where
  pretty {q} () = pretty (PTT True NoParens, the (Context q Z) [])

export
ShowQ q => Show (TT q Z) where
  show = render " " . pretty ()

export
showTm : ShowQ q => Context q n -> TT q n -> String
showTm ctx tm = render "  " $ pretty (PTT False NoAppParens, ctx) tm

export
ShowQ q => Pretty () (Context q n) where
  pretty () Nil = neutral
  pretty () [b] = parens (pretty (Context.Nil {q}) b)
  pretty () (b :: bs) = pretty () bs <++> parens (pretty bs b)
