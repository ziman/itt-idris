module ITT.Module

import public ITT.Core
import public Utils.Pretty
import Inference.Evar
import ITT.Pretty
import Data.SortedMap as Map
import Data.SortedSet as Set

public export
data Body : (q : Type) -> Type where
  Abstract : Body q     -- postulates, primitives, ..., not a value
  Constructor : Body q  -- is a value
  Term : TT q Z -> Body q

public export
Backtrace : Type
Backtrace = List String

public export
data Constr : Type where
  CEq : (v, w : Evar) -> Constr
  CLeq : (bt : Backtrace) -> (gs : SortedSet Evar) -> (v : Evar) -> Constr

public export
data DeferredEq : Type where
  DeferEq : (g : Evar) -> (bt : Backtrace) -> (ctx : Context Evar n) -> (x, y : TT Evar n) -> DeferredEq

export
Show Constr where
  show (CEq v w) = show v ++ " ~ " ++ show w
  show (CLeq bt gs v) = show (Set.toList gs) ++ " -> " ++ show v

showTm : Context Evar n -> TT Evar n -> String
showTm ctx tm = render "  " $ pretty (PTT False NoAppParens, ctx) tm

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
  (<+>) (MkConstrs cty eqs) (MkConstrs cs' eqs') = MkConstrs (cty <+> cs') (eqs <+> eqs')

export
Monoid Constrs where
  neutral = MkConstrs [] []

public export
record Def (q : Type) (cty : Type) where
  constructor D
  dn  : Name
  dq  : q
  dty : TT q Z
  db  : Body q
  dcs : cty

export
Globals : (q : Type) -> (cty : Type) -> Type
Globals q cty = SortedMap Name (Def q cty)

export
lookup : Name -> Globals q cty -> Maybe (Def q cty)
lookup = SortedMap.lookup

export
ShowQ q => Pretty () (Def q cty) where
  pretty () (D n q ty (Term tm) cs) =
    text "function"
    <++> text (show n)
    <++> text ":"
    <++> pretty (PTT False NoParens, Context.Nil) ty
    <++> text "="
    $$ indent (pretty (PTT True NoParens, Context.Nil) tm)
  pretty () (D n q ty Constructor cs) =
    text "constructor"
    <++> text (show n)
    <++> text ":"
    <++> pretty (PTT False NoParens, Context.Nil) ty
  pretty () (D n q ty Abstract cs) =
    text "postulate"
    <++> text (show n)
    <++> text ":"
    <++> pretty (PTT False NoParens, Context.Nil) ty

export
ShowQ q => Show (Def q cty) where
  show = render "  " . pretty ()

public export
record Module (q : Type) (cty : Type) where
  constructor MkModule
  definitions : List (Def q cty)

export
toGlobals : Module q cty -> Globals q cty
toGlobals (MkModule ds) = Map.fromList [(dn d, d) | d <- ds]

export
ShowQ q => Pretty () (Module q cty) where
  pretty () (MkModule ds) = vcat $
    map (\d => pretty () d $$ text "") ds

export
ShowQ q => Show (Module q cty) where
  show = render "  " . pretty ()
