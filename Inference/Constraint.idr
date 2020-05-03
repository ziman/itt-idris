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
  CUse :
    (pv : Evar)
    -> (lhs : SortedSet Evar)
    -> (rhs : List (SortedSet Evar))
    -> Constr

  CEq : (p, q : Evar) -> Constr

export
Pretty () Constr where
  pretty () (CUse pv lhs rhs) =
    text "product" <++> text (show . toList $ lhs) <++> text "≥ sum"
    $$ indentBlock
        [ text "product" <++> text (show . toList $ rhsTerm)
        | rhsTerm <- rhs
        ]

  pretty () (CEq p q) = pretty () p <++> text "~" <++> pretty () q

export
Show Constr where
  show = render "  " . pretty ()

public export
data DeferredEq : Type where
  DeferEq : (g : Evar) -> (bt : Backtrace)
    -> (ctx : Context Evar n) -> (x, y : TT Evar n) -> DeferredEq

export
Show DeferredEq where
  show (DeferEq g bt ctx x y) =
    show g ++ " -> " ++ showTm ctx x ++ " ~ " ++ showTm ctx y

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
