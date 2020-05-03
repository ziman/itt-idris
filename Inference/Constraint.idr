module Inference.Constraint

import public Core.TT
import public Core.TT.Pretty
import public Core.Context
import public Core.Globals
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
  CProdSumLeq :
    (lhs : List (List Evar))
    -> (rhs : Evar)
    -> Constr

  CProdEq :
    (lhs : List Evar)
    -> (rhs : Evar)
    -> Constr

  CProdSumLeqProd :
    (lhs : List (List Evar))
    -> (rhs : List Evar)
    -> Constr

  CEq : (lhs, rhs : Evar) -> Constr

export
Pretty () Constr where
  pretty () (CProdSumLeq lhs rhs) =
    text (show rhs) <++> text "≥ sum"
    $$ indentBlock
        [ text "product" <++> text (show term)
        | term <- lhs
        ]

  pretty () (CProdSumLeqProd lhs rhs) =
    text "product" <++> text (show rhs) <++> text "≥ sum"
    $$ indentBlock
        [ text "product" <++> text (show term)
        | term <- lhs
        ]

  pretty () (CProdEq lhs rhs) =
    text (show rhs) <++> text "~ product" <++> text (show lhs)

  pretty () (CEq lhs rhs) = pretty () rhs <++> text "~" <++> pretty () lhs

export
Show Constr where
  show = render "  " . pretty ()

export
isCEq : Constr -> Bool
isCEq (CEq _ _) = True
isCEq _ = False

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

export
toConstrs : Globals Evar -> SortedMap Name (List (List Evar)) -> Either Name (List Constr)
toConstrs gs = traverse toConstr . toList
  where
    toConstr : (Name, List (List Evar)) -> Either Name Constr
    toConstr (n, gss) =
      case lookup n gs of
        Just d => Right $ CProdSumLeq gss d.binding.qv
        Nothing => Left n
