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
  prettyTelescope : ShowQ q => Context q n -> Telescope q n pn -> Telescope q (pn + n) s -> List Doc
  prettyTelescope ctx pvs [] = []
  prettyTelescope ctx pvs (B n q ty :: bs) =
    parens (
      text n <++> text ":" <++> pretty (PTT False NoParens, bs ++ pvs ++ ctx) ty
    ) :: prettyTelescope ctx pvs bs

  prettyScrut : ShowQ q => Context q n -> Binding q (pv + n) -> Telescope q n pv -> TT q n -> Doc
  prettyScrut ctx (B n q Erased) pvs tm =
    text n
    <++> text "="
    <++> pretty (PTT False NoParens, ctx) tm

  prettyScrut ctx (B n q ty) pvs tm =
    text n
    <++> text ":"
    <++> pretty (PTT False NoParens, pvs ++ ctx) ty
    <++> text "="
    <++> pretty (PTT False NoParens, ctx) tm

  prettyScruts : ShowQ q => Context q n -> Telescope q n pn -> Vect pn (TT q n) -> List Doc
  prettyScruts ctx [] [] = []
  prettyScruts ctx (b::bs) (s::ss) = prettyScrut ctx b bs s :: prettyScruts ctx bs ss

  export
  ShowQ q => Pretty (PrettyTT, Context q n) (TT q n) where
    pretty (PTT top nl, ctx) (V i) = case lookup i ctx of
      B n q' ty => text n
    pretty (PTT True nl,  ctx) (Lam b rhs) = parensFrom NoAppParens nl $
      text "\\" <+> pretty ctx b <+> text "."
      $$ indent (pretty (PTT True NoParens, b::ctx) rhs)
    pretty (PTT False nl, ctx) (Lam b rhs) = parensFrom NoAppParens nl $
      text "\\" <+> pretty ctx b <+> text "."
      <++> pretty (PTT True NoParens, b::ctx) rhs
    pretty (PTT top nl, ctx) (Pi b rhs) = parensFrom NoAppParens nl $
      parens (pretty ctx b)
      <++> text "->" <++> pretty (PTT False NoParens, b::ctx) rhs
    pretty (PTT top nl, ctx) (App q' f x) = parensFrom UseParens nl $
      pretty (PTT False NoAppParens, ctx) f 
      <+> text (showApp q')
      <+> pretty (PTT False UseParens, ctx) x
    pretty (PTT top nl, ctx) Star = text "Type"
    pretty (PTT top nl, ctx) Erased = text "_"
    pretty (PTT top nl, ctx) Bool_ = text "Bool"
    pretty (PTT True nl, ctx) (If_ c t e) = parensFrom NoAppParens nl $
      text "if" <++> pretty (PTT False NoParens, ctx) c
      $$ indent (text "then" <++> pretty (PTT True NoParens, ctx) t)
      $$ indent (text "else" <++> pretty (PTT True NoParens, ctx) e)
    pretty (PTT False nl, ctx) (If_ c t e) = parensFrom NoAppParens nl $
      text "if"
      <++> pretty (PTT False NoParens, ctx) c
      <++> text "then" <++> pretty (PTT False NoParens, ctx) t
      <++> text "else" <++> pretty (PTT False NoParens, ctx) e
    pretty (PTT top nl, ctx) True_ = text "True"
    pretty (PTT top nl, ctx) False_ = text "False"

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