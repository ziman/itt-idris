module Smt

data SExp : Type where
  A : String -> SExp     -- atom
  L : List SExp -> SExp  -- list

record Smt (ty : Type) where
  constructor MkSmt
  sexp : SExp

data SmtError : Type where
  OtherError : String -> SmtError

record SmtState where
  constructor MkSmtState

record SmtM (a : Type) where
  constructor MkSmtM
  runSmtM : SmtState -> Either SmtError (SmtState, List SExp, a)

Functor SmtM where
  map f (MkSmtM g) = MkSmtM $ \st => case g st of
    Left err => Left err
    Right (st', ss, x) => Right (st', ss, f x)

Applicative SmtM where
  pure x = MkSmtM $ \st => Right (st, neutral, x)
  (<*>) (MkSmtM f) (MkSmtM g) = MkSmtM $ \st =>
    case f st of
      Left err => Left err
      Right (st', ss', f') => case g st' of
        Left err => Left err
        Right (st'', ss'', x'') => Right (st'', ss' <+> ss'', f' x'')

Monad SmtM where
  (>>=) (MkSmtM f) g = MkSmtM $ \st => case f st of
    Left err => Left err
    Right (st', ss', x') => case runSmtM (g x') st' of
      Left err => Left err
      Right (st'', ss'', x'') => Right (st'', ss' <+> ss'', x'')

tell : List SExp -> SmtM ()
tell ss = MkSmtM $ \st => Right (st, ss, ())

tellL : List SExp -> SmtM ()
tellL xs = tell [L xs]

mitm : SmtM a -> SmtM (List SExp, a)
mitm (MkSmtM f) = MkSmtM $ \st => case f st of
  Left err => Left err
  Right (st', ss, x) => Right (st', neutral, (ss, x))

get : SmtM SmtState
get = MkSmtM $ \st => Right (st, neutral, st)

put : SmtState -> SmtM ()
put st = MkSmtM $ \_ => Right (st, neutral, ())

modify : (SmtState -> SmtState) -> SmtM ()
modify f = MkSmtM $ \st => Right (f st, neutral, ())

throw : SmtError -> SmtM a
throw err = MkSmtM $ \_ => Left err

interface SmtValue a where
  smtShow : a -> SExp
  smtRead : SExp -> Maybe a

interface SmtEnum a where
  smtEnumValues : List a

SmtValue Bool where
  smtShow True = A "true"
  smtShow False = A "false"

  smtRead (A "true") = Just True
  smtRead (A "false") = Just False
  smtRead _ = Nothing

SmtValue Int where
  smtShow i = A (show i)
  smtRead (A s) = Just $ cast s  -- TODO: error checking
  smtRead _ = Nothing

SmtValue Integer where
  smtShow i = A (show i)
  smtRead (A s) = Just $ cast s  -- TODO: error checking
  smtRead _ = Nothing

SmtEnum Bool where
  smtEnumValues = [False, True]

Prop : Type
Prop = Smt Bool

record SmtType (a : Type) where
  constructor MkSmtType
  sexp : SExp

record SmtFun (args : List Type) (ret : Type) where
  constructor MkSmtFun
  sexp : SExp

smtInt : SmtType Int
smtInt = MkSmtType (A "Int")

smtBool : SmtType Bool
smtBool = MkSmtType (A "Bool")

declEnum : (SmtValue a, SmtEnum a) => (n : String) -> SmtM (SmtType a)
declEnum {a} n = do
  tellL
      [ A "declare-datatypes"
      , L []
      , L [L $ A n :: map (smtShow . the a) smtEnumValues]
      ]
  pure $ MkSmtType (A n)

data SmtTyList : List Type -> Type where
  Nil : SmtTyList []
  (::) : SmtType a -> SmtTyList as -> SmtTyList (a :: as)

private
binop : (SmtValue a, SmtValue b) => String -> Smt a -> Smt b -> Smt c
binop op (MkSmt x) (MkSmt y) = MkSmt $ L [A op, x, y]

Pred2 : Type
Pred2 = {a, b : Type}
    ->(SmtValue a, SmtValue b)
    => Smt a -> Smt b -> Smt Bool

infix 2 .==
(.==) : Pred2
(.==) = binop "="

infix 2 .<=
(.<=) : Pred2
(.<=) = binop "<="

infix 2 .<
(.<) : Pred2
(.<) = binop "<"

lit : SmtValue a => a -> Smt a
lit = MkSmt . smtShow

assert : Smt Bool -> SmtM ()
assert (MkSmt x) = tellL [A "assert", x]

assertEq : (SmtValue a, SmtValue b)
    => Smt a -> Smt b
    -> SmtM ()
assertEq x y = assert $ x .== y

declFun2 : (SmtValue a, SmtValue b, SmtValue c)
    => (n : String)
    -> SmtType a -> SmtType b -> SmtType c
    -> SmtM (Smt a -> Smt b -> Smt c)
declFun2 n ta tb tc = do
  tell
    [ L
      [ A "declare-fun"
      , A n
      , L [sexp ta, sexp tb]
      , sexp tc
      ]
    ]
  pure $ \(MkSmt sx), (MkSmt sy) => MkSmt (L [A n, sx, sy])

defineEnumFun2
  : (SmtValue a, SmtValue b, SmtValue c, SmtEnum a, SmtEnum b)
  => (n : String)
  -> SmtType a -> SmtType b -> SmtType c
  -> (a -> b -> c)
  -> SmtM (Smt a -> Smt b -> Smt c)
defineEnumFun2 n ta tb tc f = do
  g <- declFun2 n ta tb tc
  for_ smtEnumValues $ \x =>
    for_ smtEnumValues $ \y =>
      assertEq (g (lit x) (lit y)) (lit $ f x y)
  pure g

declVar : (n : String) -> (ty : SmtType a) -> SmtM (Smt a)
declVar n (MkSmtType ty) = do
  tell [L [A "declare-const", A n, ty]]
  pure $ MkSmt (A n)
