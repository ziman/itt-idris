module Core.TC

import public Core.Context
import public Core.Globals
import public Core.Normalise

%default total
%undotted_record_projections off

public export
interface Error e where
  fromEvalError : Normalise.EvalError -> e

public export
Backtrace : Type
Backtrace = List Doc

public export
record Failure (e : Type) where
  constructor MkF
  backtrace : Backtrace
  error : e

export
Show e => Show (Failure e) where
  show (MkF bt err) = render "  " $
    text "With backtrace:"
    $$ indentBlock bt
    $$ show err

public export
record TCResult (w : Type) (a : Type) where
  constructor MkR
  output : w
  value : a

export
Functor (TCResult w) where
  map f (MkR w x) = MkR w (f x)

export
Monoid w => Applicative (TCResult w) where
  pure x = MkR neutral x
  MkR w f <*> MkR w' x = MkR (w <+> w') (f x)

record Env (q : Type) (n : Nat) where
  constructor MkE
  backtrace : List Doc
  globals : Globals q
  context : Context q n

-- only this namespace has access to the internals of the TC monad
-- this is to keep it as small as clean as possible
namespace Core
  export
  record TC (e : Type) (w : Type) (q : Type) (n : Nat) (a : Type) where
    constructor MkTC
    run : Env q n -> Either (Failure e) (TCResult w a)

  export
  run : Monoid w => Globals q -> Context q n -> TC e w q n a -> Either (Failure e) (TCResult w a)
  run gs ctx tc = tc.run (MkE neutral gs ctx)

  export
  Functor (TC e w q n) where
    map f (MkTC g) = MkTC $ \env => map f <$> g env

  export
  Monoid w => Applicative (TC e w q n) where
    pure x = MkTC $ \env => pure (pure x)
    MkTC f <*> MkTC g = MkTC $ \env => [| f env <*> g env |]

  export
  Monoid w => Monad (TC e w q n) where
    (>>=) (MkTC f) g = MkTC $ \env => do
      MkR w  x <- f env
      MkR w' y <- (g x).run env
      pure $ MkR (w <+> w') y

  export
  withEnv : (Env q n -> Env q m) -> TC e w q m a -> TC e w q n a
  withEnv f (MkTC g) = MkTC $ g . f

  export
  getEnv : Monoid w => (Env q n -> a) -> TC e w q n a
  getEnv f = MkTC $ \env => Right (MkR neutral $ f env)

  export
  emit : w -> TC e w q n ()
  emit w = MkTC $ \env => Right (MkR w ())

  export
  throw : e -> TC e w q n a
  throw err = MkTC $ \env => Left (MkF env.backtrace err)

export
getGlobals : Monoid w => TC e w q n (Globals q)
getGlobals = getEnv (.globals)

export
withBnd : Binding q n -> TC e w q (S n) a -> TC e w q n a
withBnd b = withEnv record { context $= (b ::) }

export
withCtx : Context q n -> TC e w q n a -> TC e w q Z a
withCtx [] tc = tc
withCtx (b :: bs) tc = withCtx bs $ withBnd b tc

export
redTC : (Error e, Monoid w) => Form -> TT q n -> TC e w q n (TT q n)
redTC form tm = do
  gs <- getGlobals
  case red form gs tm of
    Left e => throw $ fromEvalError e
    Right tm' => pure tm'
