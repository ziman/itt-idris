module Inference.Constraint

import public Core.TT
import public Core.TT.Pretty
import public Core.Context
import public Inference.Evar
import public Data.SortedSet
import public Data.SortedMap
import public Utils.Pretty

%default total
%undotted_record_projections off

public export
Backtrace : Type
Backtrace = List String

public export
data Constr : Type where
  CSumLeq :
    (ubnd : Evar)
    -> (terms : List (List Evar))
    -> Constr

  CProdEq :
    (result : Evar)
    -> (factors : List Evar)
    -> Constr

  CEq : (p, q : Evar) -> Constr

export
Pretty () Constr where
  pretty () (CSumLeq ubnd terms) =
    text (show ubnd) <++> text "≥ sum"
    $$ indentBlock
        [ text "product" <++> text (show term)
        | term <- terms
        ]

  pretty () (CProdEq q qs) =
    text (show q) <++> text "~ product" <++> text (show qs)

  pretty () (CEq p q) = pretty () p <++> text "~" <++> pretty () q

export
Show Constr where
  show = render "  " . pretty ()

public export
record DeferredEq where
  constructor DeferEq
  {0 n : Nat}
  trigger : Evar
  backtrace : Backtrace
  context : Context Evar n
  lhs : TT Evar n
  rhs : TT Evar n

export
Show DeferredEq where
  show (DeferEq t bt ctx x y) =
    show t ++ " -> " ++ showTm ctx x ++ " ~ " ++ showTm ctx y

public export
record Constrs where
  constructor MkConstrs
  constrs : List Constr
  deferredEqs : List DeferredEq

export
Semigroup Constrs where
  (<+>) (MkConstrs cs eqs) (MkConstrs cs' eqs')
    = MkConstrs (cs <+> cs') (eqs <+> eqs')

export
Monoid Constrs where
  neutral = MkConstrs [] []
