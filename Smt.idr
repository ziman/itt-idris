module Smt

import System
import Text.Lexer
import Text.Parser

%default total

public export
data SmtError : Type where
  Unsatisfiable : SmtError
  SmtFileError : FileError -> SmtError
  OtherError : String -> SmtError
  LexError : Int -> Int -> String -> SmtError

export
Show SmtError where
  show (OtherError msg) = msg
  show (SmtFileError err) = show err
  show Unsatisfiable = "unsatisfiable"
  show (LexError row col rest) = "could not lex at " ++ show (row, col) ++ ": " ++ rest

public export
data SExp : Type where
  A : String -> SExp     -- atom
  L : List SExp -> SExp  -- list

Show SExp where
  show = show'
    where
      mutual
        show' : SExp -> String
        show' (A s) = s
        show' (L xs) = "(" ++ showL xs ++ ")"

        showL : List SExp -> String
        showL [] = ""
        showL [x] = show' x
        showL (x :: xs) = show' x ++ " " ++ showL xs

private
data SToken = ParL | ParR | Atom String | Space

private
lexSExp : String -> Either SmtError (List (TokenData SToken))
lexSExp src = case lex tokens src of
    (ts, (_, _, "")) => Right $ filter notSpace ts
    (_, (row, col, rest)) => Left $ LexError row col rest
  where
    notSpace : TokenData SToken -> Bool
    notSpace td = case tok td of
        Space => False
        _ => True

    atom : Lexer
    atom = some $ pred (\x => not (isSpace x || x == '(' || x == ')'))

    tokens : TokenMap SToken
    tokens =
      [ (is '(', const ParL)
      , (is ')', const ParR)
      , (atom,   Atom)
      , (pred isSpace, const Space)
      ]

export
record Smt (ty : Type) where
  constructor MkSmt
  sexp : SExp

private
record SmtState where
  constructor MkSmtState

export
record SmtM (a : Type) where
  constructor MkSmtM
  runSmtM' : SmtState -> Either SmtError (SmtState, List SExp, a)

export
runSmtM : SmtM () -> Either SmtError String
runSmtM (MkSmtM f) = case f MkSmtState of
  Left err => Left err
  Right (_st, ss, ()) => Right . unlines $ map show ss

export
Functor SmtM where
  map f (MkSmtM g) = MkSmtM $ \st => case g st of
    Left err => Left err
    Right (st', ss, x) => Right (st', ss, f x)

export
Applicative SmtM where
  pure x = MkSmtM $ \st => Right (st, neutral, x)
  (<*>) (MkSmtM f) (MkSmtM g) = MkSmtM $ \st =>
    case f st of
      Left err => Left err
      Right (st', ss', f') => case g st' of
        Left err => Left err
        Right (st'', ss'', x'') => Right (st'', ss' <+> ss'', f' x'')

export
Monad SmtM where
  (>>=) (MkSmtM f) g = MkSmtM $ \st => case f st of
    Left err => Left err
    Right (st', ss', x') => case runSmtM' (g x') st' of
      Left err => Left err
      Right (st'', ss'', x'') => Right (st'', ss' <+> ss'', x'')

private
tell : List SExp -> SmtM ()
tell ss = MkSmtM $ \st => Right (st, ss, ())

private
tellL : List SExp -> SmtM ()
tellL xs = tell [L xs]

private
mitm : SmtM a -> SmtM (List SExp, a)
mitm (MkSmtM f) = MkSmtM $ \st => case f st of
  Left err => Left err
  Right (st', ss, x) => Right (st', neutral, (ss, x))

private
get : SmtM SmtState
get = MkSmtM $ \st => Right (st, neutral, st)

private
put : SmtState -> SmtM ()
put st = MkSmtM $ \_ => Right (st, neutral, ())

private
modify : (SmtState -> SmtState) -> SmtM ()
modify f = MkSmtM $ \st => Right (f st, neutral, ())

private
throw : SmtError -> SmtM a
throw err = MkSmtM $ \_ => Left err

public export
interface SmtValue a where
  smtShow : a -> SExp
  smtRead : SExp -> Maybe a

public export
interface SmtEnum a where
  smtEnumValues : List a

export
SmtValue Bool where
  smtShow True = A "true"
  smtShow False = A "false"

  smtRead (A "true") = Just True
  smtRead (A "false") = Just False
  smtRead _ = Nothing

export
SmtValue Int where
  smtShow i = A (show i)
  smtRead (A s) = Just $ cast s  -- TODO: error checking
  smtRead _ = Nothing

export
SmtValue Integer where
  smtShow i = A (show i)
  smtRead (A s) = Just $ cast s  -- TODO: error checking
  smtRead _ = Nothing

export
SmtEnum Bool where
  smtEnumValues = [False, True]

public export
Prop : Type
Prop = Smt Bool

export
record SmtType (a : Type) where
  constructor MkSmtType
  sexp : SExp

export
record SmtFun (args : List Type) (ret : Type) where
  constructor MkSmtFun
  sexp : SExp

export
smtInt : SmtType Int
smtInt = MkSmtType (A "Int")

export
smtBool : SmtType Bool
smtBool = MkSmtType (A "Bool")

export
declEnum : (SmtValue a, SmtEnum a) => (n : String) -> SmtM (SmtType a)
declEnum {a} n = do
  tellL
      [ A "declare-datatypes"
      , L []
      , L [L $ A n :: map (smtShow . the a) smtEnumValues]
      ]
  pure $ MkSmtType (A n)

private
binop : (SmtValue a, SmtValue b) => String -> Smt a -> Smt b -> Smt c
binop op (MkSmt x) (MkSmt y) = MkSmt $ L [A op, x, y]

public export
Pred2 : Type
Pred2 = {a, b : Type}
    ->(SmtValue a, SmtValue b)
    => Smt a -> Smt b -> Smt Bool

infix 2 .==
export
(.==) : Pred2
(.==) = binop "="

infix 2 .<=
export
(.<=) : Pred2
(.<=) = binop "<="

infix 2 .<
export
(.<) : Pred2
(.<) = binop "<"

export
lit : SmtValue a => a -> Smt a
lit = MkSmt . smtShow

export
assert : Smt Bool -> SmtM ()
assert (MkSmt x) = tellL [A "assert", x]

export
assertEq : (SmtValue a, SmtValue b)
    => Smt a -> Smt b
    -> SmtM ()
assertEq x y = assert $ x .== y

export
smtError : String -> Smt a
smtError msg = MkSmt $ L [A "error", A $ "\"" ++ msg ++ "\""] -- bad hack

export
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

export
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

export
declVar : (n : String) -> (ty : SmtType a) -> SmtM (Smt a)
declVar n (MkSmtType ty) = do
  tell [L [A "declare-const", A n, ty]]
  pure $ MkSmt (A n)

public export
Solution : Type
Solution = ({a : Type} -> SmtValue a => Smt a -> Maybe a)

private
parseSolution : String -> Either SmtError Solution
parseSolution src = ?rhs

export
solve : SmtM () -> IO (Either SmtError Solution)
solve model =
    case runSmtM model' of
      Left err => pure $ Left err
      Right src => do
        -- WARNING: incredibly bad code follows
        writeFile "/tmp/model.smt" src
        System.system "z3 -in -smt2 /tmp/model.smt > /tmp/solution.smt"
        Right sol <- readFile "/tmp/solution.smt"
            | Left err => pure (Left (SmtFileError err))
        pure $ parseSolution sol
  where
    model' : SmtM ()
    model' = model *> tell [L [A "check-sat"], L [A "get-model"]]
