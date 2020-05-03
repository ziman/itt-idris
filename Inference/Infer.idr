module Inference.Infer

import Utils.Misc
import Core.TT.Lens
import public Core.TT
import public Core.TT.Pretty
import public Core.Context
import public Core.Normalise
import public Inference.Evar
import public Inference.Constraint
import public Utils.OrdSemiring

import Data.Fin
import Data.List
import Data.Strings
import Data.SortedSet

%default total
%undotted_record_projections off

public export
Set : Type -> Type
Set = SortedSet

public export
Term : Nat -> Type
Term = TT Evar

public export
Ty : Nat -> Type
Ty = TT Evar

public export
record TCState where
  constructor MkTCS

public export
data ErrorMessage : Nat -> Type where
  CantConvert : TT Evar n -> TT Evar n -> ErrorMessage n
  NotPi : TT () n -> ErrorMessage n
  CantInferErased : ErrorMessage n
  CantInferWildcard : ErrorMessage n
  NotImplemented : ErrorMessage n
  QuantityMismatch : Q -> Q -> ErrorMessage n
  WhnfError : EvalError -> ErrorMessage n
  UnknownGlobal : Name -> ErrorMessage n
  OverconstrainedBinding : Fin n -> ErrorMessage n
  UnderconstrainedBinding : Fin n -> ErrorMessage n
  Debug : Doc -> ErrorMessage n

showEM : Context () n -> ErrorMessage n -> String
showEM ctx (CantConvert x y)
    = "can't convert: " ++ showTm ctx (eraseQ ttQ x) ++ " with " ++ showTm ctx (eraseQ ttQ y)
showEM ctx (NotPi x)
    = "not a pi: " ++ showTm ctx x
showEM ctx CantInferErased
    = "can't infer types for erased terms"
showEM ctx CantInferWildcard
    = "can't infer types for pattern wildcards"
showEM ctx NotImplemented
    = "WIP: not implemented yet"
showEM ctx (QuantityMismatch q q')
    = "quantity mismatch: " ++ show q ++ " /= " ++ show q'
showEM ctx (UnknownGlobal n)
    = "unknown global: " ++ show n
showEM ctx (WhnfError e)
    = "reduction error: " ++ show e
showEM ctx (OverconstrainedBinding i)
    = "conflicting constraints for " ++ show (lookup i ctx).name
showEM ctx (UnderconstrainedBinding i)
    = "underconstrained binder: " ++ show (lookup i ctx).name
showEM ctx (Debug doc)
    = render "  " (text ">>> DEBUG <<< " $$ indent doc)

public export
record Failure cq where
  constructor MkF
  backtrace : Backtrace
  {0 n : Nat}
  context : Context cq n
  errorMessage : ErrorMessage n

export
Show (Failure cq) where
  show (MkF bt ctx msg) = "With backtrace:\n"
    ++ unlines (reverse $ map ("  " ++) bt)
    ++ showEM (eraseQ contextQ ctx) msg

public export
record Env (q : Type) (n : Nat) where
  constructor MkE
  guards : List Evar
  globals : Globals Evar
  context : Context q n
  backtrace : Backtrace

mkLU : Maybe (List lu, Fin n) -> Context cq n -> Vect n (List lu)
mkLU Nothing [] = []
mkLU Nothing (_ :: bs) = [] :: mkLU Nothing bs
mkLU (Just (lu,   FZ)) (_ :: bs) = lu :: mkLU Nothing bs
mkLU (Just (lu, FS i)) (_ :: bs) = [] :: mkLU (Just (lu, i)) bs

noLU : Context cq n -> Vect n (List lu)
noLU = mkLU Nothing

public export
record TCResult (lu : Type) (n : Nat) (a : Type) where
  constructor MkR
  state : TCState
  constrs : List Constr
  deferredEqs : List DeferredEq
  localUsage : Vect n (List lu)
  globalUsage : SortedMap Name (List (List Evar))
  value : a

Functor (TCResult lu n) where
  map f = record { value $= f }

public export
record TC (cq : Type) (lu : Type) (n : Nat) (a : Type) where
  constructor MkTC
  run : Env cq n -> TCState -> Either (Failure cq) (TCResult lu n a)

public export
TCR : Nat -> Type -> Type
TCR = TC (List Evar) (List Evar)

public export
TCL : Nat -> Type -> Type
TCL = TC () Evar

public export
TCC : Nat -> Type -> Type
TCC = TC () ()

export
Functor (TC cq lu n) where
  map f (MkTC g) = MkTC $ \env, st => case g env st of
    Left fail => Left fail
    Right result => Right (f <$> result)

export
Applicative (TC cq lu n) where
  pure x = MkTC $ \env, st => Right (MkR st [] [] (noLU env.context) empty x)
  (<*>) (MkTC f) (MkTC g) = MkTC $ \env, st =>
    case f env st of
      Left fail => Left fail
      Right r' => case g env r'.state of
        Left fail => Left fail
        Right r'' =>
          Right
            (MkR
              r''.state
              (r'.constrs <+> r''.constrs)
              (r'.deferredEqs <+> r''.deferredEqs)
              (zipWith (<+>) r'.localUsage r''.localUsage)
              (mergeWith (<+>) r'.globalUsage r''.globalUsage)
              (r'.value r''.value))

export
Monad (TC cq lu n) where
  (>>=) (MkTC f) g = MkTC $ \env, st =>
    case f env st of
      Left fail => Left fail
      Right r' => case g r'.value of
        MkTC h => case h env r'.state of
          Left fail => Left fail
          Right r'' =>
            Right
              (MkR
                r''.state
                (r'.constrs <+> r''.constrs)
                (r'.deferredEqs <+> r''.deferredEqs)
                (zipWith (<+>) r'.localUsage r''.localUsage)
                (mergeWith (<+>) r'.globalUsage r''.globalUsage)
                r''.value)

getEnv : TC cq lu n (Env cq n)
getEnv = MkTC $ \env, st => Right (MkR st [] [] (noLU env.context) empty env)

getCtx : TC cq lu n (Context cq n)
getCtx = .context <$> getEnv

getGlobals : TC cq lu n (Globals Evar)
getGlobals = .globals <$> getEnv

throw : ErrorMessage n -> TC cq lu n a
throw msg = MkTC $ \env, st
    => Left (MkF env.backtrace env.context msg)

throwDebug : Doc -> TC cq lu n a
throwDebug = throw . Debug

withBndR : Binding (List Evar) n -> TCR (S n) a -> TCR n a
withBndR b@(B n pqs ty) (MkTC f) = MkTC $ \(MkE gs globs ctx bt), st =>
  case f (MkE gs globs (b :: ctx) bt) st of
    Left fail
      => Left fail
    Right (MkR st' cs eqs (lu :: lus) gus x)
      => Right (MkR st (CUse pqs lu :: cs) eqs lus gus x)

withCtxR : Context (List Evar) n -> TCR n a -> TCR Z a
withCtxR [] tc = tc
withCtxR (b :: bs) tc = withCtxR bs $ withBndR b tc

withBndL : Binding () n -> TCL (S n) a -> TCL n (List Evar, a)
withBndL (B n () ty) (MkTC f) = MkTC $ \(MkE gs globs ctx bt), st =>
  case f (MkE gs globs (B n () ty :: ctx) bt) st of
    Left fail
      => Left fail
    Right (MkR st' cs eqs (lu :: lus) gus x)
      => Right (MkR st cs eqs lus gus (lu, x))

withCtxL : Context () n -> TCL n a -> TCL Z (Vect n (List Evar), a)
withCtxL [] tc = (\x => ([], x)) <$> tc
withCtxL (b :: bs) tc = do
  (lus, (lu, x)) <- withCtxL bs $ withBndL b tc
  pure (lu :: lus, x)

withBnd : Binding cq n -> TC cq () (S n) a -> TC cq () n a
withBnd b (MkTC f) = MkTC $ \env, st =>
  -- we can discard usage because we know that it's useless {lu = ()}
  record { localUsage $= tail} <$>
    f (record { context $= (b ::) } env) st

withCtx : Context cq n -> TC cq () n a -> TC cq () Z a
withCtx [] tc = tc
withCtx (b :: bs) tc = withCtx bs $ withBnd b tc

withGuard : Evar -> TC cq lu n a -> TC cq lu n a
withGuard q (MkTC f) = MkTC $ \(MkE gs globs ctx bt), st
    => f (MkE (q :: gs) globs ctx bt) st

use : Fin n -> TCR n ()
use i = MkTC $ \env, st =>
  Right (MkR st [] [] (mkLU (Just ([env.guards], i)) env.context) empty ())

provide : Fin n -> TCL n ()
provide i = MkTC $ \env, st =>
  Right (MkR st [] [] (mkLU (Just (env.guards, i)) env.context) empty ())

useGlobal : Name -> TCR n ()
useGlobal n = MkTC $ \env, st =>
  Right (MkR st [] [] (noLU env.context) (insert n [env.guards] empty) ())

useCtorTag : Q -> TCL n ()
useCtorTag q = MkTC $ \env, st =>
  -- constructor tags are always linearly bound
  -- (which means you can't force linearly bound patterns)
  --
  -- consider a linearly bound bool pattern: there's no other variables
  -- so you have to at least inspect the tag to satisfy linearity
  --
  -- Small trick: rhs = [[q]] ~= sum [product [q]] = sum [q] = q
  -- So this constraint says that q uses must be allowable here:
  --   product guards >= q
  --
  -- For forced patterns, q = I; for checking patterns, q = L
  Right (MkR st [CUse env.guards [[QQ q]]] [] (noLU env.context) empty ())

irrelevant : TC cq lu n a -> TC cq lu' n a
irrelevant (MkTC f) = MkTC $ \env, st =>
  record { localUsage = noLU env.context } <$> f env st

infix 3 ~~
(~~) : Evar -> Evar -> TC cq lu n ()
(~~) (QQ p) (QQ q) =
  if p == q
    then pure ()
    else throw $ QuantityMismatch p q
(~~) p q = MkTC $ \env, st =>
  Right (MkR st [CEq p q] [] (noLU env.context) empty ())

lookup : Fin n -> TC cq lu n (Binding cq n)
lookup i = lookup i <$> getCtx

lookupGlobal : Name -> TC cq lu n (Binding Evar n)
lookupGlobal n =
  (lookup n <$> getGlobals) >>= \case
    Nothing => throw $ UnknownGlobal n
    Just d => pure $ weakenClosedBinding d.binding

trace : Show tr => tr -> TC cq lu n a -> TC cq lu n a
trace t (MkTC f) = MkTC $ \(MkE gs globs ctx bt), st
  => f (MkE gs globs ctx (show t :: bt)) st

traceDoc : Show tr => Doc -> tr -> TC cq lu n a -> TC cq lu n a
traceDoc doc t (MkTC f) = MkTC $ \(MkE gs globs ctx bt), st
  => let msg = render "  " (text (show t) <+> text ": " <++> doc)
      in f (MkE gs globs ctx (msg :: bt)) st

traceTm : (Show tr, ShowQ q) => TT q n -> tr -> TC cq lu n a -> TC cq lu n a
traceTm tm t (MkTC f) = MkTC $ \(MkE gs globs ctx bt), st
  => let msg = show t ++ ": " ++ showTm ctx tm
      in f (MkE gs globs ctx (msg :: bt)) st

traceCtx : (Show tr, Pretty (Context cq n) b) => b -> tr -> TC cq lu n a -> TC cq lu n a
traceCtx bv t (MkTC f) = MkTC $ \(MkE gs globs ctx bt), st
  => let msg = show t ++ ": " ++ (render "  " $ pretty ctx bv)
      in f (MkE gs globs ctx (msg :: bt)) st

deferEq : Evar -> Term n -> Term n -> TC cq lu n ()
deferEq g x y =
  -- heuristic:
  -- do a quick syntactic check first
  -- and if that succeeds, we needn't worry about equalities
  if x == y
    then pure ()
    else MkTC $ \(MkE gs globs ctx bt), st
      => Right
        ( MkR st []
          [DeferEq g bt
            (eraseQ contextQ ctx)
            (eraseQ ttQ x)
            (eraseQ ttQ y)
          ]
          (noLU ctx)
          empty
          ())

whnfTC : Term n -> TC cq () n (Term n)
whnfTC tm = do
  gs <- getGlobals
  case red WHNF gs tm of
    Left e => throw $ WhnfError e
    Right tm' => pure tm'

mutual
  infix 3 ~=
  covering export
  (~=) : Term n -> Term n -> TC cq lu n ()
  (~=) p q = irrelevant $ do
    p' <- whnfTC p
    q' <- whnfTC q
    conv p' q'

  covering
  conv : Term n -> Term n -> TC cq () n ()
  conv (P n) (P n') =
    if n == n'
      then pure ()
      else throw $ CantConvert (P n) (P n')

  conv (V i) (V j) = case finEq i j of
    True  => pure ()
    False => throw $ CantConvert (V i) (V j)

  conv l@(Lam b@(B n q ty) rhs) r@(Lam b'@(B n' q' ty') rhs') = do
    q ~~ q'
    ty ~= ty'
    withBnd (B n q ty) $ rhs ~= rhs'

  conv l@(Pi b@(B n q ty) rhs) r@(Pi b'@(B n' q' ty') rhs') = do
    q ~~ q'
    ty ~= ty'
    withBnd (B n q ty) $ rhs ~= rhs'

  conv l@(App q f x) r@(App q' f' x') = do
    q ~~ q'
    f ~= f'
    case q of
      QQ I => pure ()
      QQ _ => x ~= x'
      EV _ => deferEq q x x'
  conv Type_ Type_ = pure ()
  conv l r = throw $ CantConvert l r

covering export
resumeEq : DeferredEq -> TC () () n ()
resumeEq (DeferEq g bt ctx x y) = MkTC $ \env, st =>
  case x ~= y of
    MkTC f => f (MkE [] env.globals ctx bt) st

covering export
inferTm : Term n -> TCR n (Ty n)
inferTm tm@(P n) = traceTm tm "GLOB" $ do
  b <- lookupGlobal n
  useGlobal n
  pure $ b.type

inferTm tm@(V i) = traceTm tm "VAR" $ do
  b <- lookup i
  use i
  pure $ b.type

inferTm tm@(Lam b@(B n q ty) rhs) = traceTm tm "LAM" $ do
  tyTy <- irrelevant $ inferTm ty
  tyTy ~= Type_

  Pi b <$> withBndR (B n [q] ty) $ inferTm rhs

inferTm tm@(Pi b@(B n q ty) rhs) = traceTm tm "PI" $ do
  tyTy <- irrelevant $ inferTm ty
  tyTy ~= Type_

  withBndR (B n [q] ty) $ do
    rhsTy <- irrelevant $ inferTm rhs
    rhsTy ~= Type_

  pure Type_

inferTm tm@(App f x) = traceTm tm "APP" $ do
  fTy <- whnfTC =<< inferTm f
  case fTy of
    Pi b@(B piN piQ piTy) piRhs => do
      xTy <- withGuard piQ $ inferTm x
      traceTm fTy "fTy" $
        xTy ~= piTy

      pure $ subst (substFZ x) piRhs

    _ => throw $ NotPi fTy

inferTm Type_ = pure Type_
inferTm Erased = throw CantInferErased

mutual
  covering export
  inferPat : Evar -> Pat Evar n -> TCL n (Ty n)
  inferPat fq pat@(PV i) = traceCtx pat "PV" $ do
    b <- lookup i
    provide i
    pure b.type

  inferPat fq pat@(PCtorApp ctor args) = traceCtx pat "PAPP" $ do
    -- we don't construct the value so we don't place requirements on the quantity of the constructor
    -- it could happen that the constructor is never constructed
    -- in such cases, the whole pattern clause can be erased
    cTy <- case ctor of
      Forced cn => do
        b <- lookupGlobal cn
        -- no inspection here so the guards must be okay with this (L won't be!)
        useCtorTag I
        pure b.type
      Checked cn => do
        b <- lookupGlobal cn
        -- inspect the constructor tag exactly once
        useCtorTag L
        pure b.type

    -- the remaining arguments use the same guards
    -- because they're disjoint from tag inspection
    inferPatApp fq cTy args

  inferPat fq pat@(PForced tm) = traceCtx pat "PFORCED" $
    -- just check type-correctness
    irrelevant $ inferTm tm

  inferPat fq PWildcard =
    throw CantInferWildcard

  covering export
  inferPatApp : Evar -> TT Evar n -> List (Evar, Pat Evar n) -> TCL n (Ty n)
  inferPatApp fq fTy [] = pure fTy
  inferPatApp fq fTy ps@(pat :: pats) = traceCtx (PCtorApp (Checked (UN "_")) ps) "PAT-APP" $ do
    -- if we have gs applications
    -- then we will have (appQ :: gs) subpatterns available
    whnfTC fTy >>= \case
      Pi b@(B piN piQ piTy) piRhs => do
        patTy <- withGuard piQ $ inferPat fq pat
        patTy ~= piTy

        -- remaining args use the same guards
        -- because they're disjoint
        inferPatApp fq
          (subst (substFZ $ patToTm pat) piRhs)
          pats

      _ => throw $ NotPi fTy

covering export
inferBinding : Binding () n -> TCC n ()
inferBinding bnd@(B n () ty) = traceCtx bnd "BINDING" $ do
  tyTy <- irrelevant $ inferTm ty
  tyTy ~= Type_

covering export
inferCtx : Context () n -> TCC Z ()
inferCtx [] = pure ()
inferCtx (b :: bs) = do
  inferCtx bs
  withCtx bs $ traceCtx b "CTX-BND" $ do
    inferBinding b

covering export
inferClause : Binding Evar Z -> {argn : Nat} -> Clause Evar argn -> TCC Z ()
inferClause fbnd c@(MkClause pi lhs rhs) = traceDoc (pretty (UN fbnd.name) c) "CLAUSE" $ do
  -- check the context
  inferCtx pi

  -- check the LHS and get the provided quantities for patvars
  (piQ, lhsTy) <- withCtxL pi $ traceCtx (PCtorApp (Checked (UN fbnd.name)) lhs) "CLAUSE-LHS" $
    inferPatApp fbnd.qv (weakenClosed fbnd.type) (toList lhs)

  -- with the provided quantities, check the RHS
  rhsTy <- withCtxR piQ $ traceTm rhs "CLAUSE-RHS" $
    inferTm rhs

  -- check that the types match
  -- this can be done in the plain old context
  withCtx pi $ traceTm lhsTy "CLAUSE-CONV" $ do
    lhsTy ~= rhsTy

covering export
inferBody : Binding Evar Z -> Body Evar -> TCC Z ()
inferBody fbnd Postulate = pure ()
inferBody fbnd Constructor = pure ()
inferBody fbnd (Foreign _) = pure ()
inferBody fbnd (Clauses argn cs) = traverse_ (inferClause fbnd) cs

covering export
inferDefinition : Definition Evar -> TCC Z ()
inferDefinition d@(MkDef bnd body) = traceDoc (pretty () d) "DEF" $ do
  inferBinding bnd
  inferBody bnd body

covering export
inferGlobals : TCC Z ()
inferGlobals = do
  gs <- Globals.toList <$> getGlobals
  traverse_ inferDefinition gs
