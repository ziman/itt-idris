module Inference.Constraint

import public Core.TT
import public Core.TT.Pretty
import public Core.Context
import public Inference.Evar
import public Data.SortedSet
import public Data.SortedMap

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

public export
record Equality where
  constructor MkEq
  v, w : Evar

public export
record Sum where
  constructor MkSum
  result : Evar
  inputs : List (SortedSet Evar)

public export
record Max where
  constructor MkMax
  result : Evar
  inputs : SortedSet Evar

public export
record CollectedConstrs where
  constructor MkCC
  equalities : List Equality
  sums : SortedMap Evar (List (SortedSet Evar))
  maxes : SortedMap Evar (SortedSet Evar)

export
collect : List Constr -> CollectedConstrs
collect cs =
  MkCC
    (foldr addEq [] cs)
    (foldr addSum empty cs)
    (foldr addMax empty cs)
  where
    addEq : Constr -> List Equality -> List Equality
    addEq (CEq v w) xs = MkEq v w :: xs
    addEq _ xs = xs

    addSum : Constr -> SortedMap Evar (List (SortedSet Evar)) -> SortedMap Evar (List (SortedSet Evar)) 
    addSum (CSum bt gs v) cs = mergeWith (++) (insert v [gs] empty) cs
    addSum _ cs = cs

    addMax : Constr -> SortedMap Evar (SortedSet Evar) -> SortedMap Evar (SortedSet Evar)
    addMax (CMax bt u v) cs = mergeWith union (insert v (insert u empty) empty) cs
    addMax _ cs = cs
