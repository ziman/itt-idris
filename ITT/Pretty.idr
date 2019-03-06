module ITT.Pretty

import public ITT.Core
import public Utils.Pretty

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
  ShowQ q => Pretty (Context q n) (Def q n) where
    pretty ctx (D n dq ty (Abstract _))
      = text n <++> text (showCol dq) <++> pretty (PTT False NoParens, ctx) ty
    pretty ctx d@(D n dq ty (Term tm)) =
      text n <++> text (showCol dq) <++> pretty (PTT False NoParens, ctx) ty
      <++> text "=" <++> pretty (PTT True NoParens, d :: ctx) tm

  export
  ShowQ q => Pretty (PrettyTT, Context q n) (TT q n) where
    pretty (PTT top nl, ctx) (V i) = text . defName $ lookupCtx i ctx
    pretty (PTT True nl,  ctx) (Bind Lam d rhs) = parensFrom NoAppParens nl $
      text "\\" <+> pretty ctx d <+> text "."
      $$ indent (pretty (PTT True NoParens, d::ctx) rhs)
    pretty (PTT False nl, ctx) (Bind Lam d rhs) = parensFrom NoAppParens nl $
      text "\\" <+> pretty ctx d <+> text "."
      <++> pretty (PTT True NoParens, d::ctx) rhs
    pretty (PTT top nl, ctx) (Bind Pi d rhs) = parensFrom NoAppParens nl $
      parens (pretty ctx d)
      <++> text "->" <++> pretty (PTT False NoParens, d::ctx) rhs
    pretty (PTT top nl, ctx) (Bind Let d rhs) = parensFrom NoAppParens nl $
      text "let" <++> pretty ctx d
      $$ indent (text "in" <++> pretty (PTT True NoParens, d::ctx) rhs)
    pretty (PTT top nl, ctx) (App q' f x) = parensFrom UseParens nl $
      pretty (PTT False NoAppParens, ctx) f 
      <+> text (showApp q')
      <+> pretty (PTT False UseParens, ctx) x
    pretty (PTT top nl, ctx) Star = text "Type"
    pretty (PTT top nl, ctx) Erased = text "_"

export
ShowQ q => Pretty () (TT q Z) where
  pretty () = pretty (PTT True NoParens, TT.Nil)

export
ShowQ q => Show (TT q Z) where
  show = render " " . pretty ()
