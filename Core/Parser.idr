module Core.Parser

import public Core.Globals

import Core.TT
import Core.Clause

import Text.Lexer
import Text.Lexer.Core
import Text.Parser
import Text.Parser.Core
import Data.List
import Data.Vect

%default total

data Token
  = Ident String
  | ParL
  | ParR
  | BraceL
  | BraceR
  | SqBrL
  | SqBrR
  | Lam
  | SquigArrow
  | Arrow
  | Equals
  | DblArrow
  | Comma
  | Dot
  | Space
  | Comment
  | Underscore
  | Pipe
  | Colon (Maybe Q)
  | Keyword String

Show Token where
  show (Ident s) = "identifier " ++ show s
  show ParL = "("
  show ParR = ")"
  show BraceL = "{"
  show BraceR = "}"
  show SqBrL = "["
  show SqBrR = "]"
  show Lam = "\\"
  show Arrow = "->"
  show SquigArrow = "->"
  show Equals = "="
  show DblArrow = "=>"
  show Comma = ","
  show Dot = "."
  show Space = "(space)"
  show Comment = "(comment)"
  show Underscore = "_"
  show Pipe = "|"
  show (Colon mbQ) = "colon " ++ show mbQ
  show (Keyword kwd) = "keyword " ++ show kwd

Eq Token where
  (==) x y = case (x, y) of
    (Ident x, Ident y) => x == y
    (ParL, ParL) => True
    (ParR, ParR) => True
    (BraceL, BraceL) => True
    (BraceR, BraceR) => True
    (SqBrL, SqBrL) => True
    (SqBrR, SqBrR) => True
    (Lam, Lam) => True
    (Arrow, Arrow) => True
    (SquigArrow, SquigArrow) => True
    (Dot, Dot) => True
    (Space, Space) => True
    (Equals, Equals) => True
    (DblArrow, DblArrow) => True
    (Comma, Comma) => True
    (Comment, Comment) => True
    (Pipe, Pipe) => True
    (Underscore, Underscore) => True
    (Colon mq, Colon mq') => mq == mq'
    (Keyword x, Keyword y) => x == y
    _ => False

public export
data ParseError : Type where
  LexError : Int -> Int -> String -> ParseError
  SyntaxError : Int -> Int -> String -> List (TokenData Token) -> ParseError

export
Show ParseError where
  show (LexError r c msg) = "lex error at " ++ show (r, c) ++ ": " ++ msg
  show (SyntaxError r c msg ts) = "syntax error at " ++ show (r, c) ++ ": " ++ msg
    ++ "; next up: " ++ show [TokenData.tok t | t <- take 8 ts]

lex : String -> Either ParseError (List (TokenData Token))
lex src = case lex tokens src of
    (ts, (_, _, "")) => Right $ filter notSpace ts
    (_, (r, c, rest)) => Left $ LexError r c rest
  where
    notSpace : TokenData Token -> Bool
    notSpace td = case tok td of
      Space   => False
      Comment => False
      _ => True

    ident : Lexer
    ident = some $ pred (\x => isAlpha x || isDigit x || x == '_' || x == '\'')

    colon : Lexer
    colon = is ':' <+> opt (is 'I' <|> is 'E' <|> is 'L' <|> is 'R')

    parseColon : String -> Token
    parseColon ":I" = Colon (Just I)
    parseColon ":E" = Colon (Just E)
    parseColon ":L" = Colon (Just L)
    parseColon ":R" = Colon (Just R)
    parseColon _ = Colon Nothing

    kwdOrIdent : String -> Token
    kwdOrIdent s =
        if s `elem` keywords
          then Keyword s
          else Ident   s
      where
        keywords : List String
        keywords =
          [ "Type", "foreign", "postulate", "data", "where", "end", "forall"
          ]

    tokens : TokenMap Token
    tokens = 
      [ (is '(',       const ParL)
      , (is ')',       const ParR)
      , (is '{',       const BraceL)
      , (is '}',       const BraceR)
      , (is '[',       const SqBrL)
      , (is ']',       const SqBrR)
      , (is '_',       const Underscore)
      , (is '|',       const Pipe)
      , (ident,        kwdOrIdent)
      , (is '\\',      const Lam)
      , (exact "->" ,  const Arrow)
      , (exact "~>" ,  const SquigArrow)
      , (is '.',       const Dot)
      , (is ',',       const Comma)
      , (exact "=>",   const DblArrow)
      , (is '=',       const Equals)
      , (space,        const Space)
      , (colon,        parseColon)
      , (lineComment (exact "--"), const Comment)
      ]

Term : Nat -> Type
Term = TT (Maybe Q) 

Ty : Nat -> Type
Ty = TT (Maybe Q)

Rule : Type -> Type
Rule = Grammar (TokenData Token) True

token : Token -> Rule ()
token t = terminal ("expecting " ++ show t) $ \t' =>
  if t == tok t'
    then Just ()
    else Nothing

kwd : String -> Rule ()
kwd s = token (Keyword s)

lookupName : Eq a => a -> Vect n a -> Maybe (Fin n)
lookupName x [] = Nothing
lookupName x (y :: ys) =
  if x == y
    then Just FZ
    else FS <$> lookupName x ys

ident : Rule String
ident = terminal "identifier" $ \t => case tok t of
  Ident n => Just n
  _ => Nothing

varName : Vect n String -> Rule (Fin n)
varName ns = do
    n <- ident
    aux n ns (lookupName n ns)  -- case block does not typecheck here
  where
    aux : String -> Vect n String -> Maybe (Fin n) -> Grammar (TokenData Token) False (Fin n)
    aux n ns (Just i) = pure i
    aux n ns Nothing = fail $ "variable " ++ show n
      ++ " not found in scope " ++ show ns

var : Vect n String -> Rule (Term n)
var ns = V <$> varName ns

ref : Vect n String -> Rule (Term n)
ref ns = V <$> varName ns

parens : {c : _} -> Grammar (TokenData Token) c a -> Rule a
parens p = token ParL *> p <* token ParR

colon : Rule (Maybe Q)
colon = terminal "colon" $ \t => case tok t of
  Colon mq => Just mq
  _ => Nothing

record Scruts (n : Nat) where
  constructor MkScruts
  s_pn : Nat
  s_pvs : Telescope (Maybe Q) n s_pn
  s_ss  : Vect s_pn (Term n)
  s_pns : Vect s_pn String

record Tele (npn : Nat) where
  constructor MkTele
  t_s : Nat
  t_tele : Telescope (Maybe Q) npn t_s
  t_names : Vect t_s String

mutual
  binding : Vect n String -> Rule (Binding (Maybe Q) n)
  binding ns = B <$> ident <*> colon <*> term ns

  lam : Vect n String -> Rule (Term n)
  lam ns = do
    token Lam
    commit
    b <- binding ns
    token Dot
    Lam b <$> term (b.name :: ns)

  pi : Vect n String -> Rule (Term n)
  pi ns = do
    b <- parens $ binding ns
    token Arrow
    commit
    Pi b <$> term (b.name :: ns)

  atom : Vect n String -> Rule (Term n)
  atom ns = ref ns
    <|> (kwd "Type" *> pure Type_)
    <|> (parens $ term ns)

  -- includes nullary applications (= variables)
  app : Vect n String -> Rule (Term n)
  app ns = do
    head <- atom ns
    commit
    args <- many (atom ns)
    Empty $ foldl (App Nothing) head args

  term : Vect n String -> Rule (Term n)
  term ns
    = lam ns
    <|> pi ns
    <|> erased
    <|> app ns

  erased : Rule (Term n)
  erased = token Underscore *> pure Erased

patAtom : Vect n String -> Rule (Pat (Maybe Q) n)
patAtom = ?rhs_patAtom

postulate_ : Rule (List (Definition (Maybe Q)))
postulate_ = do
  kwd "postulate"
  commit
  bnd <- binding []
  kwd "end"
  pure [MkDef bnd Postulate]

dataDecl : Rule (List (Definition (Maybe Q)))
dataDecl = do
  kwd "data"
  commit
  bnd <- binding []
  kwd "where"
  bnds <- sepBy (token Comma) (binding [])
  kwd "end"
  pure [MkDef b Constructor | b <- bnd :: bnds]

telescope : {k : Nat} -> Vect (k + b) String -> Telescope (Maybe Q) b k
    -> Grammar (TokenData Token) False (n ** Telescope (Maybe Q) b n)
telescope {k} ns t = option (k ** t) $ do
  b <- parens $ binding ns
  telescope (b.name :: ns) (b :: t)

names : Telescope q b n -> Vect n String
names [] = []
names (b :: bs) = b.name :: names bs

record RawClause where
  constructor MkRC
  {pn : Nat}
  pi : Context (Maybe Q) pn
  lhs : List (Pat (Maybe Q) pn)
  rhs : TT (Maybe Q) pn

rawClause : String -> Rule RawClause
rawClause fn = do
  kwd "forall"
  (pn ** pvs) <- telescope [] []
  token Dot
  let pns = names pvs
  token (Ident fn)
  pats <- many (patAtom pns)
  token SquigArrow
  rhs <- term pns
  pure $ MkRC pvs pats rhs

checkVect : (n : Nat) -> List a -> Maybe (Vect n a)
checkVect Z [] = Just []
checkVect (S n) (x :: xs) = (x ::) <$> checkVect n xs
checkVect _ _ = Nothing

checkClause : (argn : Nat) -> RawClause -> Maybe (Clause (Maybe Q) argn)
checkClause argn rc =
  checkVect argn rc.lhs <&>
    \lhs => MkClause rc.pi lhs rc.rhs

checkClauses : List RawClause -> Maybe (argn ** List (Clause (Maybe Q) argn))
checkClauses [] = Nothing
checkClauses (c :: cs) =
  let argn = length c.lhs
    in case traverse (checkClause argn) (c :: cs) of
      Nothing => Nothing
      Just cs' => Just (argn ** cs')

clauseFun : Rule (List (Definition (Maybe Q)))
clauseFun = do
  bnd <- binding []
  commit
  kwd "where"
  rcs <- sepBy1 (token Comma) (rawClause bnd.name)
  kwd "end"
  cont bnd rcs -- for some reason inference fails here
 where
  cont : Binding (Maybe Q) Z -> List RawClause -> Grammar (TokenData Token) False (List (Definition (Maybe Q)))
  cont bnd rcs =
    case checkClauses rcs of
      Nothing => fail "ill-formed clauses"
      Just (argn ** cs) => pure [MkDef bnd (Clauses argn cs)]

definitions : Rule (List (Definition (Maybe Q)))
definitions = 
  postulate_
  <|> dataDecl
  <|> clauseFun

globals : Grammar (TokenData Token) False (Globals (Maybe Q))
globals = toGlobals . concat <$> many definitions

export
parse : String -> Either ParseError (Globals (Maybe Q))
parse src = case lex src of
  Left err => Left err
  Right ts => case Text.Parser.Core.parse (globals <* eof) ts of
    Left (Error msg []) => Left $ SyntaxError 0 0 msg []
    Left (Error msg (tt :: tts)) => Left $ SyntaxError (line tt) (col tt) msg (tt :: tts)
    Right (gs, _) => Right gs
