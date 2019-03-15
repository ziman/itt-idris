module Compiler.Monad

%access export

record ITT (a : Type) where
  constructor MkITT
  runITT : IO (Either String a)

Functor ITT where
  map f (MkITT x) = MkITT $ (f <$>) <$> x

Applicative ITT where
  pure x = MkITT $ pure (Right x)
  (<*>) (MkITT f) (MkITT x) = MkITT $
    f >>= \f' => case f' of
      Left err => pure $ Left err
      Right f'' => (f'' <$>) <$> x

Monad ITT where
  (>>=) (MkITT f) g = MkITT $ f >>= \x => case x of
    Left e => pure $ Left e
    Right x => runITT (g x)

liftIO : IO a -> ITT a
liftIO = MkITT . map Right

log : String -> ITT ()
log = liftIO . putStrLn

prn : Show a => a -> ITT ()
prn = log . show

throw : String -> ITT a
throw = MkITT . pure . Left
