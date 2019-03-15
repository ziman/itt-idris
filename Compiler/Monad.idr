module Compiler.Monad

public export
record ITT (a : Type) where
  constructor MkITT
  runITT : IO a

Functor ITT where
  map f (MkITT x) = MkITT $ map f x

Applicative ITT where
  pure x = MkITT $ pure x
  (<*>) (MkITT f) (MkITT x) = MkITT $ f <*> x

Monad ITT where
  (>>=) (MkITT f) g = MkITT $ f >>= \x => runITT (g x)

log : String -> ITT ()
log = ITT . putStrLn

prn : Show a => a -> ITT ()
prn = log . show
