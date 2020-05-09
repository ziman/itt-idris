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
  NotPi : TT Evar n -> ErrorMessage n
  CantInferErased : ErrorMessage n
  CantInferWildcard : ErrorMessage n
  NotImplemented : ErrorMessage n
  QuantityMismatch : Q -> Q -> ErrorMessage n
  WhnfError : EvalError -> ErrorMessage n
  UnknownGlobal : Name -> ErrorMessage n
  OverconstrainedBinding : Fin n -> ErrorMessage n
  UnderconstrainedBinding : Fin n -> ErrorMessage n
  ConstructorArityMismatch : Binding Evar Z -> Nat -> ErrorMessage n
  Debug : Doc -> ErrorMessage n

showEM : Context Evar n -> ErrorMessage n -> String
showEM ctx (CantConvert x y)
    = "can't convert: " ++ showTm ctx x ++ " with " ++ showTm ctx y
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
showEM ctx (ConstructorArityMismatch b arity)
    = "constructor arity " ++ show arity ++ " wrong for " ++ prettyShow (Context.Nil {q=Evar}) b
showEM ctx (Debug doc)
    = render "  " (text ">>> DEBUG <<< " $$ indent doc)

public export
record Failure where
  constructor MkF
  backtrace : Backtrace
  {0 n : Nat}
  context : Context Evar n
  errorMessage : ErrorMessage n

export
Show Failure where
  show (MkF bt ctx msg) = "With backtrace:\n"
    ++ unlines (reverse $ map ("  " ++) bt)
    ++ showEM ctx msg

public export
record Env (n : Nat) where
  constructor MkE
  guards : List Evar
  globals : Globals Evar
  context : Context Evar n
  backtrace : Backtrace

mkLU : Maybe (List lu, Fin n) -> Context Evar n -> Vect n (List lu)
mkLU Nothing [] = []
mkLU Nothing (_ :: bs) = [] :: mkLU Nothing bs
mkLU (Just (lu,   FZ)) (_ :: bs) = lu :: mkLU Nothing bs
mkLU (Just (lu, FS i)) (_ :: bs) = [] :: mkLU (Just (lu, i)) bs

noLU : Context Evar n -> Vect n (List lu)
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

public export
record TC (lu : Type) (n : Nat) (a : Type) where
  constructor MkTC
  run : Env n -> TCState -> Either Failure (TCResult lu n a)

public export
TCR : Nat -> Type -> Type
TCR = TC (List Evar)

public export
TCL : Nat -> Type -> Type
TCL = TC Evar

public export
TCC : Nat -> Type -> Type
TCC = TC ()

export
Functor (TC lu n) where
  map f (MkTC g) = MkTC $ \env, st => case g env st of
    Left fail => Left fail
    Right result => Right $ record { value $= f } result

export
Applicative (TC lu n) where
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
Monad (TC lu n) where
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

getEnv : TC lu n (Env n)
getEnv = MkTC $ \env, st => Right (MkR st [] [] (noLU env.context) empty env)

getCtx : TC lu n (Context Evar n)
getCtx = .context <$> getEnv

getGlobals : TC lu n (Globals Evar)
getGlobals = .globals <$> getEnv

withMutualBlock : List (Definition Evar) -> TC lu n a -> TC lu n a
withMutualBlock ds (MkTC f) = MkTC $ \env, st =>
  f (record {globals $= \g => g `snocBlock` ds} env) st

throw : ErrorMessage n -> TC lu n a
throw msg = MkTC $ \env, st
    => Left (MkF env.backtrace env.context msg)

throwDebug : Doc -> TC lu n a
throwDebug = throw . Debug

withBndR : Binding Evar n -> TCR (S n) a -> TCR n a
withBndR b@(B n q ty) (MkTC f) = MkTC $ \(MkE gs globs ctx bt), st =>
  case f (MkE gs globs (B n q ty :: ctx) bt) st of
    Left fail
      => Left fail
    Right (MkR st' cs eqs (lu :: lus) gus x)
      => Right (MkR st (CProdSumLeq lu q :: cs) eqs lus gus x)

withCtxR : Context Evar n -> TCR n a -> TCC Z a
withCtxR (b :: bs) tc = withCtxR bs $ withBndR b tc
withCtxR [] (MkTC f) =
  MkTC $ \env, st =>
    record { localUsage = [] } <$> f env st  -- change the type of Nil

withBndL : Binding Evar n -> TCL (S n) a -> TCL n a
withBndL (B n q ty) (MkTC f) = MkTC $ \(MkE gs globs ctx bt), st =>
  case f (MkE gs globs (B n q ty :: ctx) bt) st of
    Left fail
      => Left fail
    Right (MkR st' cs eqs (lu :: lus) gus x)
      => Right (MkR st (CProdEq lu q :: cs) eqs lus gus x)

withCtxL : Context Evar n -> TCL n a -> TCC Z a
withCtxL (b :: bs) tc = withCtxL bs $ withBndL b tc
withCtxL [] (MkTC f) =
  MkTC $ \env, st =>
    record { localUsage = [] } <$> f env st  -- change the type of Nil

withBndC : Binding Evar n -> TCC (S n) a -> TCC n a
withBndC b (MkTC f) = MkTC $ \env, st =>
  -- we can discard usage because we know that it's useless {lu = ()}
  record { localUsage $= tail} <$>
    f (record { context $= (b ::) } env) st

withCtxC : Context Evar n -> TCC n a -> TCC Z a
withCtxC [] tc = tc
withCtxC (b :: bs) tc = withCtxC bs $ withBndC b tc

withGuard : Evar -> TC lu n a -> TC lu n a
withGuard q (MkTC f) = MkTC $ \(MkE gs globs ctx bt), st
    => f (MkE (q :: gs) globs ctx bt) st

addGlobalGuard : Evar -> SortedMap Name (List (List Evar)) -> SortedMap Name (List (List Evar))
addGlobalGuard q = map (map (q ::))

withGlobalGuard : Evar -> TC lu n a -> TC lu n a
withGlobalGuard q (MkTC f) = MkTC $ \env, st =>
  case f env st of
    Left fail => Left fail
    Right (MkR st cs eqs lu gu x) =>
      Right (MkR st cs eqs lu (addGlobalGuard q gu) x)

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
  Right (MkR st [CProdSumLeqProd [[QQ q]] env.guards] [] (noLU env.context) empty ())

irrelevant : TC lu n a -> TC lu' n a
irrelevant (MkTC f) = MkTC $ \env, st =>
  f env st <&>
    record
    { localUsage  = noLU env.context
    , globalUsage = empty
    , constrs $= filter isCEq
    }

infix 3 ~~
(~~) : Evar -> Evar -> TC lu n ()
(~~) (QQ p) (QQ q) =
  if p == q
    then pure ()
    else throw $ QuantityMismatch p q
(~~) p q = MkTC $ \env, st =>
  Right (MkR st [CEq p q] [] (noLU env.context) empty ())

lookup : Fin n -> TC lu n (Binding Evar n)
lookup i = lookup i <$> getCtx

lookupGlobal : Name -> TC lu n (Binding Evar n)
lookupGlobal n =
  (lookup n <$> getGlobals) >>= \case
    Nothing => throw $ UnknownGlobal n
    Just d => pure $ weakenClosedBinding d.binding

trace : String -> TC lu n a -> TC lu n a
trace msg (MkTC f) = MkTC $ \(MkE gs globs ctx bt), st
  => f (MkE gs globs ctx (msg :: bt)) st

traceDoc : Show tr => Doc -> tr -> TC lu n a -> TC lu n a
traceDoc doc t = trace $ render "  " (text (show t) <+> text ": " <++> doc)

traceTm : Show tr => Term n -> tr -> TC lu n a -> TC lu n a
traceTm tm t rhs = do
  ctx <- getCtx
  trace (show t ++ ": " ++ showTm ctx tm) rhs

traceCtx : (Show tr, Pretty (Context Evar n) b) => b -> tr -> TC lu n a -> TC lu n a
traceCtx bv t rhs = do
  ctx <- getCtx
  trace (show t ++ ": " ++ (render "  " $ pretty ctx bv)) rhs

deferEq : Evar -> Term n -> Term n -> TC lu n ()
deferEq g x y =
  -- heuristic:
  -- do a quick exact syntactic check first
  -- and if that succeeds, we needn't worry about equalities
  if x == y
    then pure ()
    else MkTC $ \(MkE gs globs ctx bt), st
      => Right (MkR st [] [DeferEq g bt globs ctx x y] (noLU ctx) empty ())

whnfTC : Term n -> TC lu n (Term n)
whnfTC tm = do
  gs <- getGlobals
  case red WHNF gs tm of
    Left e => throw $ WhnfError e
    Right tm' => pure tm'

mutual
  infix 3 ~=
  covering export
  (~=) : Term n -> Term n -> TC lu n ()
  (~=) p q = irrelevant $ do
    p' <- whnfTC p
    q' <- whnfTC q
    conv p' q'

  covering
  conv : Term n -> Term n -> TCC n ()
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
    withBndC (B n q ty) $
        rhs ~= rhs'

  conv l@(Pi b@(B n q ty) rhs) r@(Pi b'@(B n' q' ty') rhs') = do
    q ~~ q'
    ty ~= ty'
    withBndC (B n q ty) $
        rhs ~= rhs'

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
resumeEq : DeferredEq -> TCC Z ()
resumeEq (DeferEq {n} t bt gs ctx x y) = MkTC $ \_, st =>
  case the (TCC n ()) (x ~= y) of
    MkTC f => case f (MkE [] gs ctx bt) st of
      Left fail => Left fail
      Right (MkR st cs eqs lu gu x) => Right (MkR st cs eqs [] gu x)

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

  Pi b <$> withBndR b (inferTm rhs)

inferTm tm@(Pi b@(B n q ty) rhs) = traceTm tm "PI" $ do
  tyTy <- irrelevant $ inferTm ty
  tyTy ~= Type_

  withBndR b $ do
    rhsTy <- irrelevant $ inferTm rhs
    rhsTy ~= Type_

  pure Type_

inferTm tm@(App appQ f x) = traceTm tm "APP" $ do
  fTy <- whnfTC =<< inferTm f
  case fTy of
    Pi b@(B piN piQ piTy) piRhs => do
      appQ ~~ piQ
      xTy <- withGuard piQ $ inferTm x
      traceTm fTy "fTy" $
        traceTm xTy "xTy" $
          xTy ~= piTy

      pure $ subst (substFZ x) piRhs

    _ => throw $ NotPi fTy

inferTm Type_ = pure Type_
inferTm Erased = throw CantInferErased

mutual
  covering export
  inferPat : Pat Evar n -> TCL n (Ty n)
  inferPat pat@(PV i) = traceCtx pat "PV" $ do
    b <- lookup i
    provide i
    pure b.type

  inferPat pat@(PCtorApp ctor args) = traceCtx pat "PAPP" $ do
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
    inferPatApp cTy args

  inferPat pat@(PForced tm) = traceCtx pat "PFORCED" $
    -- just check type-correctness
    irrelevant $ inferTm tm

  inferPat PWildcard =
    throw CantInferWildcard

  covering export
  inferPatApp : TT Evar n -> List (Evar, Pat Evar n) -> TCL n (Ty n)
  inferPatApp fTy [] = pure fTy
  inferPatApp fTy ps@((appQ, pat) :: pats) = traceCtx (PCtorApp (Checked (UN "_")) ps) "PAT-APP" $ do
    -- if we have gs applications
    -- then we will have (appQ :: gs) subpatterns available
    whnfTC fTy >>= \case
      Pi b@(B piN piQ piTy) piRhs => do
        appQ ~~ piQ

        patTy <- withGuard piQ $ inferPat pat
        patTy ~= piTy

        -- remaining args use the same guards
        -- because they're disjoint
        inferPatApp
          (subst (substFZ $ patToTm pat) piRhs)
          pats

      _ => throw $ NotPi fTy

covering export
inferBinding : Binding Evar n -> TCC n ()
inferBinding bnd@(B n q ty) = traceCtx bnd "BINDING" $ do
  tyTy <- irrelevant $ inferTm ty
  tyTy ~= Type_

covering export
inferCtx : Context Evar n -> TCC Z ()
inferCtx [] = pure ()
inferCtx (b :: bs) = do
  inferCtx bs
  withCtxC bs $ traceCtx b "CTX-BND" $ do
    inferBinding b

covering export
inferClause : Binding Evar Z -> {argn : Nat} -> Clause Evar argn -> TCC Z ()
inferClause fbnd c@(MkClause pi lhs rhs) = traceDoc (pretty (UN fbnd.name) c) "CLAUSE" $ do
  -- check the context
  inferCtx pi

  -- check the LHS and get the provided quantities for patvars
  lhsTy <- withCtxL pi $ traceCtx (PCtorApp (Checked (UN fbnd.name)) $ toList lhs) "CLAUSE-LHS" $
    inferPatApp (weakenClosed fbnd.type) (toList lhs)

  -- with the provided quantities, check the RHS
  rhsTy <- withCtxR pi $ traceTm rhs "CLAUSE-RHS" $
    inferTm rhs

  -- check that the types match
  -- this can be done in the plain old context
  withCtxC pi $
    traceTm lhsTy "CLAUSE-CONV-LHS" $
      traceTm rhsTy "CLAUSE-CONV-RHS" $
        lhsTy ~= rhsTy

covering export
inferBody : Binding Evar Z -> Body Evar -> TCC Z ()
inferBody fbnd Postulate = pure ()
inferBody fbnd (Constructor arity) =
  if arity == piDepth fbnd.type
    then pure ()
    else throw $ ConstructorArityMismatch fbnd arity
inferBody fbnd (Foreign _) = pure ()
inferBody fbnd (Clauses argn cs) = traverse_ (inferClause fbnd) cs

covering export
inferDefinition : Definition Evar -> TCC Z ()
inferDefinition d@(MkDef bnd body) = traceDoc (pretty () d) "DEF" $ do
  inferBinding bnd
  withGlobalGuard bnd.qv $
    inferBody bnd body

covering export
inferDefinitions : List (List (Definition Evar)) -> TCC Z ()
inferDefinitions [] = pure ()
inferDefinitions (ds :: dss) =
  withMutualBlock ds $ do
    traverse_ inferDefinition ds
    inferDefinitions dss

covering export
inferGlobals : TCC Z ()
inferGlobals = inferDefinitions . Globals.toBlocks =<< getGlobals
