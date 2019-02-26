module Check

import TT

record TCState where
  constructor MkTS

Backtrace : Type
Backtrace = List String

data ErrorMessage : Type where
  OtherError : String -> ErrorMessage

record Failure where
  constructor MkF
  backtrace : Backtrace
  errorMessage : ErrorMessage

record TC (n : Nat) (a : Type) where
  constructor MkTC
  runTC : Context Q n -> TCState -> Either Failure (TCState, a)

Functor (TC n) where
  map f (MkTC g) = MkTC $ \ctx, st => case g ctx st of
    Left fail => Left fail
    Right (st', x) => Right (st', f x)

Applicative (TC n) where
  pure x = MkTC $ \ctx, st => Right (st, x)
  (<*>) (MkTC f) (MkTC g) = MkTC $ \ctx, st =>
    case f ctx st of
        Left fail => Left fail
        Right (st', f') => case g ctx st' of
            Left fail => Left fail
            Right (st'', x') => Right (st'', f' x')

Monad (TC n) where
  (>>=) (MkTC f) g = MkTC $ \ctx, st =>
    case f ctx st of
        Left fail => Left fail
        Right (st', x) => case g x of
            MkTC h => h ctx st'

getCtx : TC n (Context Q n)
getCtx = MkTC $ \ctx, st => Right (st, ctx)
