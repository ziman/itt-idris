module ITT.Clause

import ITT.Pretty  -- MOVE THIS TO PRETTY
import public ITT.Core
import public ITT.Lens
import Control.Monad.Identity

%default total

public export
data Pat : (q : Type) -> (n : Nat) -> (pn : Nat) -> Type where
  PV : (i : Fin pn) -> Pat q n pn
  PCtor : (cn : Name) -> Pat q n pn
  PForced : (tm : TT q (pn + n)) -> Pat q n pn
  PApp : q -> (f : Pat q n pn) -> (x : Pat q n pn) -> Pat q n pn

public export
record Lhs (q : Type) (n : Nat) (pn : Nat) where
  constructor L
  args : List (Pat q n pn)

public export
record Clause (q : Type) (n : Nat) where
  constructor C
  pn : Nat  -- erased, don't use!
  pvs : Telescope q n pn  -- use this instead
  lhs : Lhs q n pn
  rhs : TT q (pn + n)

namespace Lens
  adaptT : Applicative f
    => Telescope q n pn
    -> (g : Fin m -> f (TT q (pn + n)))
    -> Fin (pn + m) -> f (TT q (pn + n))
  adaptT pvs g i with (splitFin pvs i)
    | Left j = pure $ V (tackFinL j)
    | Right j = g j

  patTermVars : Telescope q n pn
    -> Traversal (Pat q m pn) (Pat q n pn) (Fin m) (TT q (pn + n))
  patTermVars pvs g (PV i) = pure $ PV i
  patTermVars pvs g (PCtor cn) = pure $ PCtor cn
  patTermVars pvs g (PApp q f x) =
    PApp q <$> patTermVars pvs g f <*> patTermVars pvs g x
  patTermVars pvs g (PForced tm) = PForced <$> ttVars (adaptT pvs g) tm

  adaptP : Applicative f
    => Telescope q n pn
    -> (g : Fin pn -> f (TT q (pn + n)))
    -> Fin (pn + n) -> f (TT q (pn + n))
  adaptP pvs g i with (splitFin pvs i)
    | Left j = g j
    | Right _ = pure $ V i

  patPatVars : Telescope q n pn
    -> Traversal (Pat q n pn) (Pat q n pn) (Fin pn) (TT q (pn + n))
  patPatVars pvs g (PV i) = PForced <$> g i
  patPatVars pvs g (PCtor cn) = pure $ PCtor cn
  patPatVars pvs g (PApp q f x) =
    PApp q <$> patPatVars pvs g f <*> patPatVars pvs g x
  patPatVars pvs g (PForced tm) = PForced <$> ttVars (adaptP pvs g) tm

mkArgs : Telescope q n pn -> List (Fin pn)
mkArgs [] = []
mkArgs (b :: ds) = FZ :: map FS (mkArgs ds)

substPat : Telescope q n pn
    -> Fin pn -> TT q (pn + n)
    -> Pat q n pn -> Pat q n pn
substPat {q} {n} {pn} pvs pv tm =
    runIdentity . patPatVars pvs g
  where
    g : Fin pn -> Identity (TT q (pn + n))
    g i with (i == pv)
      | True  = pure tm
      | False = pure $ V (tackFinL i)

substLhs : Telescope q n pn
    -> Fin pn -> TT q (pn + n)
    -> Lhs q n pn -> Lhs q n pn
substLhs pvs i tm (L args) = L $ map (substPat pvs i tm) args

weakenPat : Telescope q n pn -> Telescope q (pn + n) pn'
    -> Pat q n pn -> Pat q n (pn' + pn)
weakenPat pvs pvs' (PV i) = PV $ tackFinR pvs' i
weakenPat pvs pvs' (PCtor cn) = PCtor cn
weakenPat pvs pvs' (PApp q f x) =
  PApp q (weakenPat pvs pvs' f) (weakenPat pvs pvs' x)
weakenPat {q} {n} {pn} {pn'} pvs pvs' (PForced tm) =
    PForced $ rename gP tm
  where
    gP : Fin (pn + n) -> Fin ((pn' + pn) + n)
    gP i = replace (plusAssociative pn' pn n) $ tackFinR pvs' i

weakenLhs : Telescope q n pn -> Telescope q (pn + n) pn'
    -> Lhs q n pn -> Lhs q n (pn' + pn)
weakenLhs pvs pvs' (L args) = L $ map (weakenPat pvs pvs') args

mutual
  foldAlt :
      (pvs : Telescope q n pn)
      -> (lhs : Lhs q n pn)
      -> (s : Fin pn)
      -> (alt : Alt q n pn)
      -> List (Clause q n)
  foldAlt pvs lhs s (DefaultCase ct) = foldTree pvs lhs ct
  foldAlt pvs lhs s (CtorCase cn args ct) =
      foldTree
        (args ++ pvs)
        (substLhs
            (args ++ pvs)
            (tackFinR args s)
            (ctorApp (G cn) args)
            (weakenLhs pvs args lhs))
        ct
      -- we need to weaken all patvars in lhs here
      -- because we're adding args in front of pvs
    where
      ctorApp : TT q (pn + n) -> Telescope q (pn + n) pn' -> TT q (pn' + pn + n)
      ctorApp f [] = f
      ctorApp f (B bn bq bty :: bs) = App bq (rename FS $ ctorApp f bs) (V FZ)

  foldTree :
      (pvs : Telescope q n pn)
      -> (lhs : Lhs q n pn)
      -> (ct : CaseTree q n pn)
      -> List (Clause q n)
  foldTree pvs lhs (Leaf rhs) = [C _ pvs lhs rhs]
  foldTree pvs lhs (Forced s tm ct) = foldTree pvs (substLhs pvs s tm lhs) ct
  foldTree pvs lhs (Case s alts) =
    -- I have no clue why assert_total is needed here
    assert_total $ concatMap (foldAlt pvs lhs s) alts

export
foldMatch :
    (pvs : Telescope q n pn)
    -> (ss : Vect pn (TT q n))
    -> (ty : TT q (pn + n))
    -> (ct : CaseTree q n pn)
    -> List (Clause q n)
foldMatch {q} {n} {pn} pvs ss ty ct
    = foldTree pvs lhs ct
  where
    lhs : Lhs q n pn
    lhs = L $ map PV $ mkArgs pvs

export
ShowQ q => Pretty (PrettyTT, Context q n, Telescope q n pn) (Pat q n pn) where
  pretty (ptt, ctx, pctx) (PV i) = text $ lookupName i pctx
  pretty (ptt, ctx, pctx) (PCtor cn) = text (show cn)
  pretty (ptt, ctx, pctx) (PForced tm) = pretty (ptt, pctx ++ ctx) tm
  pretty (PTT mll UseParens, ctx, pctx) (PApp q f x) =
    parens $
        pretty (PTT False NoAppParens, ctx, pctx) f
        <++> text (showApp q)
        <++> pretty (PTT mll UseParens, ctx, pctx) x
  pretty (PTT mll _, ctx, pctx) (PApp q f x) =
    pretty (PTT False NoAppParens, ctx, pctx) f
    <++> text (showApp q)
    <++> pretty (PTT mll UseParens, ctx, pctx) x

export
ShowQ q => Pretty (Context q n, Telescope q n pn) (Lhs q n pn) where
  pretty (ctx, pctx) (L args) =
    hsep [pretty (PTT False UseParens, ctx, pctx) arg | arg <- args]

export
ShowQ q => Pretty (Context q n) (Clause q n) where
  pretty ctx (C pn pvs lhs rhs) = 
    hsep (prettyTelescope ctx [] pvs)
    <+> text "."
    <++> pretty (ctx, pvs) lhs
    <++> text "=>"
    <++> pretty (PTT True NoParens, pvs ++ ctx) rhs
