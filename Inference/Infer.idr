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
  NotPi : Ty n -> ErrorMessage n
  CantInferErased : ErrorMessage n
  CantInferWildcard : ErrorMessage n
  NotImplemented : ErrorMessage n
  QuantityMismatch : Q -> Q -> ErrorMessage n
  WhnfError : EvalError -> ErrorMessage n
  UnknownGlobal : Name -> ErrorMessage n
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
showEM ctx (Debug doc)
    = render "  " (text ">>> DEBUG <<< " $$ indent doc)

public export
record Failure where
  constructor MkF
  backtrace : Backtrace
  0 n : Nat
  context : Context Evar n
  errorMessage : ErrorMessage n

export
Show Failure where
  show (MkF bt _ ctx msg) = "With backtrace:\n"
    ++ unlines (reverse $ map ("  " ++) bt)
    ++ showEM ctx msg

public export
record Env (n : Nat) where
  constructor MkE
  guards : Set Evar
  globals : Globals Evar
  context : Context Evar n
  backtrace : Backtrace

public export
record TC (n : Nat) (a : Type) where
  constructor MkTC
  run : Env n -> TCState -> Either Failure (TCState, Constrs, a)

export
Functor (TC n) where
  map f (MkTC g) = MkTC $ \env, st => case g env st of
    Left fail => Left fail
    Right (st', cs, x) => Right (st', cs, f x)

export
Applicative (TC n) where
  pure x = MkTC $ \env, st => Right (st, neutral, x)
  (<*>) (MkTC f) (MkTC g) = MkTC $ \env, st =>
    case f env st of
        Left fail => Left fail
        Right (st', cs', f') => case g env st' of
            Left fail => Left fail
            Right (st'', cs'', x'') => Right (st'', cs' <+> cs'', f' x'')

export
Monad (TC n) where
  (>>=) (MkTC f) g = MkTC $ \env, st =>
    case f env st of
        Left fail => Left fail
        Right (st', cs, x) => case g x of
            MkTC h => case h env st' of
                Left fail => Left fail
                Right (st'', cs'', x'') => Right (st'', cs <+> cs'', x'')

getEnv : TC n (Env n)
getEnv = MkTC $ \env, st => Right (st, neutral, env)

getCtx : TC n (Context Evar n)
getCtx = .context <$> getEnv

getGlobals : TC n (Globals Evar)
getGlobals = .globals <$> getEnv

throw : ErrorMessage n -> TC n a
throw msg = MkTC $ \env, st
    => Left (MkF env.backtrace _ env.context msg)

throwDebug : Doc -> TC n a
throwDebug = throw . Debug

withBnd : Binding Evar n -> TC (S n) a -> TC n a
withBnd b@(B n q ty) (MkTC f) = MkTC $ \(MkE gs globs ctx bt), st
  => case f (MkE gs globs (b :: ctx) bt) st of
    Left fail => Left fail
    Right (st', MkConstrs cs eqs, x)
        => Right (st', MkConstrs (MkC Sum bt (SortedSet.fromList [QQ I]) q :: cs) eqs, x)

withCtx : Context Evar n -> TC n a -> TC Z a
withCtx [] tc = tc
withCtx (b :: bs) tc = withCtx bs $ withBnd b tc

withQ : Evar -> TC n a -> TC n a
withQ q (MkTC f) = MkTC $ \(MkE gs globs ctx bt), st
    => f (MkE (SortedSet.insert q gs) globs ctx bt) st

useEvar : Evar -> TC n ()
useEvar ev = MkTC $ \(MkE gs globs ctx bt), st
    => Right (st, MkConstrs [MkC Sum bt gs ev] [], ())

infix 3 ~>+
(~>+) : List Evar -> List Evar -> TC n ()
gs ~>+ qs = MkTC $ \(MkE gs' globs ctx bt), st =>
  Right (st, MkConstrs [MkC Sum bt (SortedSet.fromList gs) q | q <- qs] [], ())

infix 3 ~>
(~>) : List Evar -> List Evar -> TC n ()
gs ~> qs = MkTC $ \(MkE gs' globs ctx bt), st =>
  Right (st, MkConstrs [MkC Max bt (SortedSet.fromList gs) q | q <- qs] [], ())

eqEvar : Evar -> Evar -> TC n ()
eqEvar (QQ p) (QQ q) =
  if p == q
    then pure ()
    else throw $ QuantityMismatch p q
eqEvar p q = do
  [p] ~> [q]
  [q] ~> [p]

lookup : Fin n -> TC n (Binding Evar n)
lookup i = lookup i <$> getCtx

lookupGlobal : Name -> TC n (Binding Evar n)
lookupGlobal n =
  (lookup n <$> getGlobals) >>= \case
    Nothing => throw $ UnknownGlobal n
    Just d => pure $ weakenClosedBinding d.binding

trace : Show tr => tr -> TC n a -> TC n a
trace t (MkTC f) = MkTC $ \(MkE gs globs ctx bt), st
  => f (MkE gs globs ctx (show t :: bt)) st

traceDoc : Show tr => Doc -> tr -> TC n a -> TC n a
traceDoc doc t (MkTC f) = MkTC $ \(MkE gs globs ctx bt), st
  => let msg = render "  " (text (show t) <+> text ": " <++> doc)
      in f (MkE gs globs ctx (msg :: bt)) st

traceTm : Show tr => Term n -> tr -> TC n a -> TC n a
traceTm tm t (MkTC f) = MkTC $ \(MkE gs globs ctx bt), st
  => let msg = show t ++ ": " ++ showTm ctx tm
      in f (MkE gs globs ctx (msg :: bt)) st

traceCtx : (Show tr, Pretty (Context Evar n) b) => b -> tr -> TC n a -> TC n a
traceCtx bv t (MkTC f) = MkTC $ \(MkE gs globs ctx bt), st
  => let msg = show t ++ ": " ++ (render "  " $ pretty ctx bv)
      in f (MkE gs globs ctx (msg :: bt)) st

deferEq : Evar -> Term n -> Term n -> TC n ()
deferEq g x y =
  -- heuristic:
  -- do a quick syntactic check first
  -- and if that succeeds, we needn't worry about equalities
  if x == y
    then pure ()
    else MkTC $ \(MkE gs globs ctx bt), st
          => Right (st, MkConstrs [] [DeferEq g bt ctx x y], ())

whnfTC : Term n -> TC n (Term n)
whnfTC tm = do
  gs <- getGlobals
  case red WHNF gs tm of
    Left e => throw $ WhnfError e
    Right tm' => pure tm'

mutual
  infix 3 ~=
  covering export
  (~=) : Term n -> Term n -> TC n ()
  (~=) p q = do
    p' <- whnfTC p
    q' <- whnfTC q
    conv p' q'

  covering
  conv : Term n -> Term n -> TC n ()
  conv (P n) (P n') =
    if n == n'
      then pure ()
      else throw $ CantConvert (P n) (P n')

  conv (V i) (V j) = case finEq i j of
    True  => pure ()
    False => throw $ CantConvert (V i) (V j)

  conv l@(Lam b@(B n q ty) rhs) r@(Lam b'@(B n' q' ty') rhs') = do
    eqEvar q q'
    ty ~= ty'
    withBnd b $ rhs ~= rhs'

  conv l@(Pi b@(B n q ty) rhs) r@(Pi b'@(B n' q' ty') rhs') = do
    eqEvar q q'
    ty ~= ty'
    withBnd b $ rhs ~= rhs'

  conv l@(App q f x) r@(App q' f' x') = do
    eqEvar q q'
    f ~= f'
    case q of
      QQ I => pure ()
      QQ _ => x ~= x'
      EV _ => deferEq q x x'
  conv Type_ Type_ = pure ()
  conv l r = throw $ CantConvert l r

covering export
resumeEq : DeferredEq -> TC n ()
resumeEq (DeferEq g bt ctx x y) = MkTC $ \env, st =>
  case x ~= y of
    MkTC f => f (MkE SortedSet.empty env.globals ctx bt) st

covering export
inferTm : Term n -> TC n (Ty n)
inferTm tm@(P n) = traceTm tm "GLOB" $ do
  b <- lookupGlobal n
  useEvar b.qv
  pure $ b.type

inferTm tm@(V i) = traceTm tm "VAR" $ do
  b <- lookup i
  useEvar b.qv
  pure $ b.type

inferTm tm@(Lam b@(B n q ty) rhs) = traceTm tm "LAM" $ do
  tyTy <- withQ (QQ I) $ inferTm ty
  tyTy ~= Type_

  Pi b <$> (withBnd b $ inferTm rhs)

inferTm tm@(Pi b@(B n q ty) rhs) = traceTm tm "PI" $ do
  tyTy <- withQ (QQ I) $ inferTm ty
  tyTy ~= Type_

  withBnd b $ do
    rhsTy <- withQ (QQ I) $ inferTm rhs
    rhsTy ~= Type_

  pure Type_

inferTm tm@(App appQ f x) = traceTm tm "APP" $ do
  fTy <- whnfTC =<< inferTm f
  xTy <- withQ appQ $ inferTm x
  case fTy of
    Pi b@(B piN piQ piTy) piRhs => do
      traceTm fTy "fTy" $ xTy ~= piTy
      eqEvar appQ piQ
      pure $ subst (substFZ x) piRhs

    _ => throw $ NotPi fTy

inferTm Type_ = pure Type_
inferTm Erased = throw CantInferErased

mutual
  covering export
  inferPat : Evar -> List Evar -> Pat Evar n -> TC n (Ty n)
  inferPat fq gs pat@(PV i) = traceCtx pat "PV" $ do
    b <- lookup i
    [b.qv] ~>+ gs
    pure b.type

  inferPat fq gs pat@(PCtorApp ctor args) = traceCtx pat "PAPP" $ do
    cTy <- case ctor of
      Forced cn => do
        b <- lookupGlobal cn
        pure b.type
      Checked cn => do
        b <- lookupGlobal cn

        -- we don't construct the value so we don't place requirements on the quantity of the constructor
        -- if the function is bound at least L
        -- then we want to have the constructor bound at least L (but never require more)
        [QQ L, fq] ~> [b.qv]

        -- inspect the constructor tag once
        -- guaranteed to be disjoint with other inspections
        -- so we use a max-constraint
        [QQ L] ~> gs

        pure b.type

    inferPatApp fq gs cTy args

  inferPat fq gs pat@(PForced tm) = traceCtx pat "PFORCED" $
    withQ (QQ I) $ inferTm tm

  inferPat fq gs PWildcard =
    throw CantInferWildcard

  covering export
  inferPatApp : Evar -> List Evar -> TT Evar n -> List (Evar, Pat Evar n) -> TC n (Ty n)
  inferPatApp fq gs fTy [] = pure fTy
  inferPatApp fq gs fTy ps@((appQ, pat) :: pats) = traceCtx (PCtorApp (Checked (UN "_")) ps) "PAT-APP" $ do
    patTy <- inferPat fq (appQ :: gs) pat
    whnfTC fTy >>= \case
      Pi b@(B piN piQ piTy) piRhs => do
        patTy ~= piTy
        eqEvar appQ piQ
        inferPatApp fq gs
          (subst (substFZ $ patToTm pat) piRhs)
          pats

      _ => throw $ NotPi fTy

covering export
inferBinding : Binding Evar n -> TC n ()
inferBinding bnd@(B n q ty) = traceCtx bnd "BINDING" $ do
  tyTy <- withQ (QQ I) $ inferTm ty
  tyTy ~= Type_

covering export
inferCtx : Context Evar n -> TC Z ()
inferCtx [] = pure ()
inferCtx (b :: bs) = do
  inferCtx bs
  withCtx bs $ traceCtx b "CTX-BND" $ do
    inferBinding b

covering export
inferClause : Binding Evar Z -> {argn : Nat} -> Clause Evar argn -> TC Z ()
inferClause fbnd c@(MkClause pi lhs rhs) = traceDoc (pretty (UN "_") c) "CLAUSE" $ do
  inferCtx pi
  withCtx pi $ do
    lhsTy <- inferPatApp fbnd.qv [] (weakenClosed fbnd.type) (toList lhs)
    rhsTy <- inferTm rhs  -- we always need to construct one of RHS per call
    traceTm lhsTy "CLAUSE-CONV" $ do
      lhsTy ~= rhsTy

covering export
inferBody : Binding Evar Z -> Body Evar -> TC Z ()
inferBody fbnd Postulate = pure ()
inferBody fbnd Constructor = pure ()
inferBody fbnd (Foreign _) = pure ()
inferBody fbnd (Clauses argn cs) = traverse_ (inferClause fbnd) cs

covering export
inferDefinition : Definition Evar -> TC Z ()
inferDefinition d@(MkDef bnd body) = traceDoc (pretty () d) "DEF" $ do
  inferBinding bnd
  inferBody bnd body

covering export
inferGlobals : TC Z ()
inferGlobals = do
  gs <- Globals.toList <$> getGlobals
  traverse_ inferDefinition gs
