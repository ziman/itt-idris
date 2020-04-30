module Inference.Constraint

import public Core.TT
import public Core.TT.Pretty
import public Core.Context
import public Inference.Evar
import public Data.SortedSet

%default total
%undotted_record_projections off

public export
Backtrace : Type
Backtrace = List String

public export
data Constr : Type where
  CEq : (v, w : Evar) -> Constr
  CSum : (bt : Backtrace) -> (gs : SortedSet Evar) -> (v : Evar) -> Constr
  CMax : (bt : Backtrace) -> (u : Evar) -> (v : Evar) -> Constr

export
Show Constr where
  show (CEq v w) = show v ++ " ~ " ++ show w
  show (CSum bt gs v) = show (SortedSet.toList {k=Evar} gs) ++ " ~>+ " ++ show v
  show (CMax bt u v) = show u ++ " ~> " ++ show v

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

