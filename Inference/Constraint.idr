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
data Aggregation = Sum | Max

export
Show Aggregation where
  show Sum = "Sum"
  show Max = "Max"

export
Eq Aggregation where
  Sum == Sum = True
  Max == Max = True
  _ == _ = False

public export
record Constr where
  constructor MkC
  aggregation : Aggregation
  backtrace : Backtrace
  factors : SortedSet Evar
  result : Evar

export
Show Constr where
  show (MkC agg bt gs v) = show v ++ " ≥ " ++ show agg ++ " " ++ show (toList gs)

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

public export
record Collected (agg : Aggregation) where
  constructor MkCollected
  result : Evar
  inputs : List (List Evar)

export
{agg : Aggregation} -> Pretty () (Collected agg) where
  pretty {agg} () c =
    pretty () c.result <++> text "≥" <++> text (show agg)
    $$ indentBlock
     [ text "product " <++> text (show evs)
     | evs <- c.inputs
     ]

public export
record CollectedConstrs where
  constructor MkCC
  sums : List (Collected Sum)
  maxes : List (Collected Max)

export
Pretty () CollectedConstrs where
  pretty () ccs =
    text "Sums:"
    $$ indent (vcat $ map (pretty ()) ccs.sums)
    $$ text ""
    $$ text "Maxes:"
    $$ indent (vcat $ map (pretty ()) ccs.maxes)
    $$ text ""

export
collect : List Constr -> CollectedConstrs
collect cs =
  MkCC
    (map collected . toList $ foldr (add Sum) empty cs)
    (map collected . toList $ foldr (add Max) empty cs)
  where
    add : Aggregation -> Constr -> SortedMap Evar (List (SortedSet Evar)) -> SortedMap Evar (List (SortedSet Evar)) 
    add agg (MkC agg' bt gs v) cs =
      if agg == agg'
        then mergeWith (++) (insert v [gs] empty) cs
        else cs

    collected : {agg : Aggregation} -> (Evar, List (SortedSet Evar)) -> Collected agg
    collected (result, inputs) = MkCollected result (map toList inputs)
