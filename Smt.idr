module Smt

data SExp : Type where
  A : String -> SExp     -- atom
  L : List SExp -> SExp  -- list

record Smt (ty : Type) where
  constructor MkSmt
  sexp : SExp

data Z3Error : Type where
  OtherError : String -> Z3Error

record Z3State where
  constructor MkZ3State

record Z3 (a : Type) where
  constructor MkZ3
  runZ3 : Z3State -> Either Z3Error (Z3State, List SExp, a)

Functor Z3 where
  map f (MkZ3 g) = MkZ3 $ \st => case g st of
    Left err => Left err
    Right (st', ss, x) => Right (st', ss, f x)

Applicative Z3 where
  pure x = MkZ3 $ \st => Right (st, neutral, x)
  (<*>) (MkZ3 f) (MkZ3 g) = MkZ3 $ \st =>
    case f st of
      Left err => Left err
      Right (st', ss', f') => case g st' of
        Left err => Left err
        Right (st'', ss'', x'') => Right (st'', ss' <+> ss'', f' x'')

Monad Z3 where
  (>>=) (MkZ3 f) g = MkZ3 $ \st => case f st of
    Left err => Left err
    Right (st', ss', x') => case runZ3 (g x') st' of
      Left err => Left err
      Right (st'', ss'', x'') => Right (st'', ss' <+> ss'', x'')

tell : List SExp -> Z3 ()
tell ss = MkZ3 $ \st => Right (st, ss, ())

mitm : Z3 a -> Z3 (List SExp, a)
mitm (MkZ3 f) = MkZ3 $ \st => case f st of
  Left err => Left err
  Right (st', ss, x) => Right (st', neutral, (ss, x))

get : Z3 Z3State
get = MkZ3 $ \st => Right (st, neutral, st)

put : Z3State -> Z3 ()
put st = MkZ3 $ \_ => Right (st, neutral, ())

modify : (Z3State -> Z3State) -> Z3 ()
modify f = MkZ3 $ \st => Right (f st, neutral, ())

throw : Z3Error -> Z3 a
throw err = MkZ3 $ \_ => Left err

data SmtTy : Type -> Type where
  Ty : (a : Type) -> SmtTy a

interface SmtValue a where
  smtShowTy : SmtTy a -> String

  smtShow : a -> String
  smtRead : String -> Maybe a

interface SmtEnum a where
  smtEnumValues : List a

declEnum : (a : Type) -> (SmtValue a, SmtEnum a) => Z3 ()
declEnum a = tell $ [L
  [ A "declare-datatypes"
  , L []
  , L [L $ A (smtShowTy $ Ty a) :: map (A . smtShow . the a) smtEnumValues]
  ]]
