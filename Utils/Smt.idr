module Utils.Smt

import System
import System.File
import Text.Lexer
import Text.Parser
import Text.Parser.Core
import Text.Lexer.Core
import Data.List
import Data.String
import Data.SortedMap

%default total
%prefix_record_projections off

public export
data SExp : Type where
  A : String -> SExp     -- atom
  L : List SExp -> SExp  -- list

record AssertionNr where
  constructor MkAN
  number : Int

Eq AssertionNr where
  MkAN x == MkAN y = x == y

Ord AssertionNr where
  compare (MkAN x) (MkAN y) = compare x y

Show AssertionNr where
  show (MkAN i) = show i

public export
data SmtError : Type -> Type where
  Unsatisfiable : (core : List al) -> SmtError al
  FileIOError : FileError -> SmtError al
  LexError : Int -> Int -> String -> SmtError al
  SmtParseError : Int -> Int -> String -> SmtError al
  StrangeSmtOutput : List SExp -> SmtError al
  NotVariable : SExp -> SmtError al
  NotInModel : String -> SmtError al
  CouldNotParse : SExp -> SmtError al
  Impossible : String -> SmtError al

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

export
Show al => Show (SmtError al) where
  show (Unsatisfiable core) = "unsatisfiable: " ++ show core
  show (FileIOError err) = show err
  show (LexError row col rest) = "could not lex at " ++ show (row, col) ++ ": " ++ rest
  show (SmtParseError row col msg) = "parse error at " ++ show (row, col) ++ ": " ++ msg
  show (StrangeSmtOutput ss) = "unrecognised SMT solver output: " ++ unlines (map show ss)
  show (NotVariable ss) = "not a variable: " ++ show ss
  show (NotInModel v) = "variable not found in model: " ++ show v
  show (CouldNotParse ss) = "could not parse model value: " ++ show ss
  show (Impossible msg) = "impossible: " ++ show msg

data SToken = ParL | ParR | Atom String | Space

lexSExp : String -> Either (SmtError al) (List (WithBounds SToken))
lexSExp src = case lex tokens src of
    (ts, (_, _, "")) => Right $ filter notSpace ts
    (_, (row, col, rest)) => Left $ LexError row col rest
  where
    notSpace : WithBounds SToken -> Bool
    notSpace td = case td.val of
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

parseSExps : String -> Either (SmtError al) (List SExp)
parseSExps src = case lexSExp src of
    Left err => Left err
    Right ts => case parse (many sexp) ts of
      Left (Error msg Nothing ::: _) => Left $ SmtParseError 0 0 msg
      Left (Error msg (Just bnd) ::: _) => Left $ SmtParseError bnd.startLine bnd.startCol msg
      Right (sx, _) => Right sx
  where
    Rule : Type -> Type
    Rule = Grammar () SToken True

    atom : Rule SExp
    atom = terminal "atom" $ \t => case t of
      Atom s => Just $ A s
      _ => Nothing

    parL : Rule ()
    parL = terminal "(" $ \t => case t of
      ParL => Just ()
      _ => Nothing

    parR : Rule ()
    parR = terminal ")" $ \t => case t of
      ParR => Just ()
      _ => Nothing

    sexp : Rule SExp
    sexp = assert_total (atom <|> do
      parL
      commit
      xs <- many sexp
      parR
      pure $ L xs
     )

export
record Smt (ty : Type) where
  constructor MkSmt
  sexp : SExp

record SmtState (al : Type) where
  constructor MkSmtState
  assertionCounter : Int
  assertionLabels : SortedMap AssertionNr al

export
record SmtM (al : Type) (a : Type) where
  constructor MkSmtM
  runSmtM' : SmtState al -> Either (SmtError al) (SmtState al, List SExp, a)

runSmtM : SmtM al a -> Either (SmtError al) (String, SortedMap AssertionNr al, a)
runSmtM (MkSmtM f) = case f (MkSmtState 0 empty) of
  Left err => Left err
  Right (st, ss, x) => Right (unlines $ map show ss, st.assertionLabels, x)

export
Functor (SmtM al) where
  map f (MkSmtM g) = MkSmtM $ \st => case g st of
    Left err => Left err
    Right (st', ss, x) => Right (st', ss, f x)

export
Applicative (SmtM al) where
  pure x = MkSmtM $ \st => Right (st, neutral, x)
  (<*>) (MkSmtM f) (MkSmtM g) = MkSmtM $ \st =>
    case f st of
      Left err => Left err
      Right (st', ss', f') => case g st' of
        Left err => Left err
        Right (st'', ss'', x'') => Right (st'', ss' <+> ss'', f' x'')

export
Monad (SmtM al) where
  (>>=) (MkSmtM f) g = MkSmtM $ \st => case f st of
    Left err => Left err
    Right (st', ss', x') => case (g x').runSmtM' st' of
      Left err => Left err
      Right (st'', ss'', x'') => Right (st'', ss' <+> ss'', x'')

tell : List SExp -> SmtM al ()
tell ss = MkSmtM $ \st => Right (st, ss, ())

tellL : List SExp -> SmtM al ()
tellL xs = tell [L xs]

mitm : SmtM al a -> SmtM al (List SExp, a)
mitm (MkSmtM f) = MkSmtM $ \st => case f st of
  Left err => Left err
  Right (st', ss, x) => Right (st', neutral, (ss, x))

get : SmtM al (SmtState al)
get = MkSmtM $ \st => Right (st, neutral, st)

put : SmtState al -> SmtM al ()
put st = MkSmtM $ \_ => Right (st, neutral, ())

modify : (SmtState al -> SmtState al) -> SmtM al ()
modify f = MkSmtM $ \st => Right (f st, neutral, ())

freshAssertionNr : al -> SmtM al AssertionNr
freshAssertionNr label = do
  nr <- MkAN . (.assertionCounter) <$> get
  modify
    { assertionCounter $= (+1)
    , assertionLabels  $= insert nr label
    }
  pure nr

throw : SmtError al -> SmtM al a
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

SmtValue AssertionNr where
  smtShow (MkAN i) = A ("a" ++ show i)
  smtRead (A s) =
    case strUncons s of
      Just ('a', is) => Just $ MkAN (cast is)
      _ => Nothing
  smtRead _ = Nothing

binop : String -> Smt a -> Smt b -> Smt c
binop op (MkSmt x) (MkSmt y) = MkSmt $ L [A op, x, y]

public export
0 Pred2 : Type
Pred2 = {0 a, b : Type} -> Smt a -> Smt b -> Smt Bool

export
(Num a, SmtValue a) => Num (Smt a) where
  (+) = binop "+"
  (*) = binop "*"
  fromInteger x = MkSmt $ smtShow (fromInteger x)

export
(Num (Smt a), Neg a) => Neg (Smt a) where
  (-) = binop "-"
  negate (MkSmt x) = MkSmt $ L [A "-", x]

export
ifte : Smt Bool -> Smt a -> Smt a -> Smt a
ifte (MkSmt b) (MkSmt t) (MkSmt e) = MkSmt $ L [A "ite", b, t, e]

export
not : Smt Bool -> Smt Bool
not (MkSmt x) = MkSmt $ L [A "not", x]

export
max : (Ord a, SmtValue a) => Smt a -> Smt a -> Smt a
max (MkSmt x) (MkSmt y) = MkSmt $ L [A "max", x, y]

export
min : (Ord a, SmtValue a) => Smt a -> Smt a -> Smt a
min (MkSmt x) (MkSmt y) = MkSmt $ L [A "min", x, y]

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
declEnum : (SmtValue a, SmtEnum a) => (n : String) -> SmtM al (SmtType a)
declEnum {a} n = do
  tellL
      [ A "declare-datatypes"
      , L []
      , L [L $ A n :: map (smtShow . the a) smtEnumValues]
      ]
  pure $ MkSmtType (A n)

infix 2 .==
export
(.==) : Pred2
(.==) = binop "="

infix 2 .<=
export
(.<=) : Pred2
(.<=) = binop "<="

infix 2 .>=
export
(.>=) : Pred2
(.>=) = binop ">="

infix 2 .<
export
(.<) : Pred2
(.<) = binop "<"

export
lit : SmtValue a => a -> Smt a
lit = MkSmt . smtShow

export
assert' : Maybe al -> Smt Bool -> SmtM al ()
assert' Nothing (MkSmt x) = tellL [A "assert", x]
assert' (Just label) (MkSmt x) = do
  nr <- freshAssertionNr label
  tellL [A "assert", L [A "!", x, A ":named", smtShow nr]]

export
assert : al -> Smt Bool -> SmtM al ()
assert = assert' . Just

export
assertEq : (SmtValue a, SmtValue b)
    => al -> Smt a -> Smt b
    -> SmtM al ()
assertEq label x y = assert label $ x .== y

export
smtError : String -> Smt a
smtError msg = MkSmt $ L [A "error", A $ "\"" ++ msg ++ "\""] -- bad hack

export
declFun2 : (SmtValue a, SmtValue b, SmtValue c)
    => (n : String)
    -> SmtType a -> SmtType b -> SmtType c
    -> SmtM al (Smt a -> Smt b -> Smt c)
declFun2 n ta tb tc = do
  tell
    [ L
      [ A "declare-fun"
      , A n
      , L [ta.sexp, tb.sexp]
      , tc.sexp
      ]
    ]
  pure applyF
 where 
   applyF : Smt a -> Smt b -> Smt c
   applyF (MkSmt sx) (MkSmt sy) = MkSmt (L [A n, sx, sy])

export
defineEnumFun2
  : (SmtValue a, SmtValue b, SmtValue c, SmtEnum a, SmtEnum b)
  => (n : String)
  -> SmtType a -> SmtType b -> SmtType c
  -> (a -> b -> c)
  -> SmtM al (Smt a -> Smt b -> Smt c)
defineEnumFun2 n ta tb tc f = do
  g <- declFun2 n ta tb tc
  for_ smtEnumValues $ \x =>
    for_ smtEnumValues $ \y =>
      assert' Nothing $ g (lit x) (lit y) .== lit (f x y)
  pure g

export
declVar : (n : String) -> (ty : SmtType a) -> SmtM al (Smt a)
declVar n (MkSmtType ty) = do
  tell [L [A "declare-const", A n, ty]]
  pure $ MkSmt (A n)

export
maximise : Smt a -> SmtM al ()
maximise (MkSmt s) = tellL [A "maximize", s]

export
minimise : Smt a -> SmtM al ()
minimise (MkSmt s) = tellL [A "minimize", s]

public export
data FList : (Type -> Type) -> List (Type, Type) -> Type where
  Nil : FList f []
  (::) : List (tag, f a) -> FList f as -> FList f ((tag, a) :: as)

parseSol : List SExp -> Either (SmtError AssertionNr) (SortedMap String SExp)
parseSol ss@[A "unsat", _, L core] =
  case the (Maybe $ List AssertionNr) (traverse smtRead core) of
    Just nrs => Left $ Unsatisfiable nrs
    Nothing => Left $ StrangeSmtOutput ss
parseSol [A "sat", L (A "model" :: ms), _] = Right varMap
  where
    parseVar : SExp -> SortedMap String SExp
    parseVar (L [A "define-fun", A n, L [], ty, val]) =
      SortedMap.fromList [(n, val)]
    parseVar _ = SortedMap.empty

    varMap : SortedMap String SExp
    varMap = foldr (SortedMap.mergeLeft . parseVar) SortedMap.empty ms

parseSol ss = Left $ StrangeSmtOutput ss

-- this is a bit ugly but the singleton case has to be special
-- because Idris can't handle (constraint, ())
public export
AllSmtValue : List (Type, Type) -> Type
AllSmtValue [] = ()
AllSmtValue [(tag, a)] = SmtValue a
AllSmtValue ((tag, a) :: as) = (SmtValue a, AllSmtValue as)

decodeVar : SortedMap String SExp -> SmtValue a -> (tag, Smt a) -> Either (SmtError al) (tag, a)
decodeVar varMap sv (tag, MkSmt (L xs)) = Left $ NotVariable (L xs)
decodeVar varMap sv (tag, MkSmt (A v)) =
  case SortedMap.lookup v varMap of
  Nothing => Left $ NotInModel v
  Just s  => case smtRead @{sv} s of
    Nothing => Left $ CouldNotParse s
    Just val => Right (tag, val)

decode : AllSmtValue as -> SortedMap String SExp -> FList Smt as -> Either (SmtError al) (FList Prelude.id as)
decode _ varMap [] = Right []
decode {as = [(tag, a)]} sv varMap [vs] = do
    vs' <- traverse (decodeVar varMap sv) vs
    pure [vs']
decode {as = (tag, a) :: _ :: as} (sv, svs) varMap (vs :: vsX :: vss) = do
    vs' <- traverse (decodeVar varMap sv) vs
    vss' <- decode svs varMap (vsX :: vss)
    pure $ vs' :: vss'

uglyWriteFile : String -> String -> IO ()
uglyWriteFile fname content = do
  Right f <- openFile fname WriteTruncate
    | Left f => pure ()
  whatever <- fPutStr f content
  closeFile f

decodeUnsatCore : SortedMap AssertionNr al -> Either (SmtError AssertionNr) a -> Either (SmtError al) a
decodeUnsatCore als (Right x) = Right x
decodeUnsatCore als (Left (Unsatisfiable core)) =
  case traverse (\nr => lookup nr als) core of
    Just labels => Left $ Unsatisfiable labels
    Nothing => Left $ Impossible "assertion label not found"
decodeUnsatCore als (Left (FileIOError x)) = Left $ FileIOError x
decodeUnsatCore als (Left (LexError x y z)) = Left $ LexError x y z
decodeUnsatCore als (Left (SmtParseError x y z)) = Left $ SmtParseError x y z
decodeUnsatCore als (Left (StrangeSmtOutput xs)) = Left $ StrangeSmtOutput xs
decodeUnsatCore als (Left (NotVariable x)) = Left $ NotVariable x
decodeUnsatCore als (Left (NotInModel x)) = Left $ NotInModel x
decodeUnsatCore als (Left (CouldNotParse x)) = Left $ CouldNotParse x
decodeUnsatCore als (Left (Impossible x)) = Left $ Impossible x

covering export
solve : AllSmtValue as => SmtM al (FList Smt as) -> IO (Either (SmtError al) (FList Prelude.id as))
solve @{asv} {as} model =
    case runSmtM model' of
      Left err => pure $ Left err
      Right (src, als, vars) => do
        -- WARNING: this is really horrible
        uglyWriteFile "/tmp/model.smt" src
        retVal <- system "z3 -in -smt2 < /tmp/model.smt > /tmp/solution.smt"
        Right sol <- readFile "/tmp/solution.smt"
            | Left err => pure (Left (FileIOError err))

        pure $
            decodeUnsatCore als (parseSExps sol >>= parseSol)
            >>= \varMap => decode asv varMap vars
  where
    model' : SmtM al (FList Smt as)
    model' = do
      tell
        -- [ L [A "set-logic", A "QF_UFLIA"]  -- explicit logic does not work well with z3
        [ L [A "set-option", A ":produce-unsat-cores", A "true"]
        , L [A "define-fun", A "min", L[L[A "x", A "Int"], L[A "y", A "Int"]], A "Int",
            L [A "ite", L [A "<", A "x", A "y"], A "x", A "y"]]
        , L [A "define-fun", A "max", L[L[A "x", A "Int"], L[A "y", A "Int"]], A "Int",
            L [A "ite", L [A "<", A "x", A "y"], A "y", A "x"]]
        ]
      vs <- model
      tell
        [ L [A "check-sat"]
        , L [A "get-model"]
        , L [A "get-unsat-core"]
        ]
      pure vs
