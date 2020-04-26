module Compiler.Monad

public export
record ITT (a : Type) where
  constructor MkITT
  runITT : IO (Either String a)

export
Functor ITT where
  map f (MkITT x) = MkITT $ (f <$>) <$> x

export
Applicative ITT where
  pure x = MkITT $ pure (Right x)
  (<*>) (MkITT f) (MkITT x) = MkITT $
    f >>= \f' => case f' of
      Left err => pure $ Left err
      Right f'' => (f'' <$>) <$> x

export
Monad ITT where
  (>>=) (MkITT f) g = MkITT $ f >>= \x => case x of
    Left e => pure $ Left e
    Right x => runITT (g x)

export
liftIO : IO a -> ITT a
liftIO = MkITT . map Right

export
log : String -> ITT ()
log = liftIO . putStrLn

export
prn : Show a => a -> ITT ()
prn = log . show

export
throw : String -> ITT a
throw = MkITT . pure . Left
