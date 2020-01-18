module Parser

import public ITT.Core
import public ITT.Module

import Text.Lexer
import Text.Parser
import Data.Vect

%default total

data Token
  = Ident String
  | ParL
  | ParR
  | SqBrL
  | SqBrR
  | Lam
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

Eq Token where
  (==) x y = case (x, y) of
    (Ident x, Ident y) => x == y
    (ParL, ParL) => True
    (ParR, ParR) => True
    (SqBrL, SqBrL) => True
    (SqBrR, SqBrR) => True
    (Lam, Lam) => True
    (Arrow, Arrow) => True
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
  SyntaxError : Int -> Int -> String -> ParseError

export
Show ParseError where
  show (LexError r c msg) = "lex error at " ++ show (r, c) ++ ": " ++ msg
  show (SyntaxError r c msg) = "syntax error at " ++ show (r, c) ++ ": " ++ msg

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
          [ "Type", "Bool"
          , "True", "False"
          , "if", "then", "else"
          ]

    tokens : TokenMap Token
    tokens = 
      [ (is '(',       const ParL)
      , (is ')',       const ParR)
      , (is '[',       const SqBrL)
      , (is ']',       const SqBrR)
      , (is '_',       const Underscore)
      , (is '|',       const Pipe)
      , (ident,        kwdOrIdent)
      , (is '\\',      const Lam)
      , (exact "->",   const Arrow)
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
token t = terminal $ \t' =>
  if t == tok t'
    then Just ()
    else Nothing

type : Rule (Term n)
type = token (Keyword "Type") *> pure Star

lookupName : Eq a => a -> Vect n a -> Maybe (Fin n)
lookupName x [] = Nothing
lookupName x (y :: ys) =
  if x == y
    then Just FZ
    else FS <$> lookupName x ys

ident : Rule String
ident = terminal $ \t => case tok t of
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

name : Rule Name
name = map (\n => N n 0) ident

ref : Vect n String -> Rule (Term n)
ref ns = V <$> varName ns

parens : Grammar (TokenData Token) c a -> Rule a
parens p = token ParL *> p <* token ParR

colon : Rule (Maybe Q)
colon = terminal $ \t => case tok t of
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
    rhs <- term (bn b :: ns)
    pure $ Lam b rhs

  pi : Vect n String -> Rule (Term n)
  pi ns = do
    token ParL
    b <- binding ns
    token ParR
    token Arrow
    commit
    rhs <- term (bn b :: ns)
    pure $ Pi b rhs

  atom : Vect n String -> Rule (Term n)
  atom ns = ref ns
    <|> (token (Keyword "Bool") *> pure Bool_)
    <|> (token (Keyword "True") *> pure True_)
    <|> (token (Keyword "False") *> pure False_)
    <|> do { token ParL; tm <- term ns; token ParR; pure tm }

  -- includes nullary applications (= variables)
  app : Vect n String -> Rule (Term n)
  app ns = do
    head <- atom ns
    commit
    args <- many (atom ns)
    pure $ foldl (App Nothing) head args

  telescope : Vect n String -> Tele n -> Grammar (TokenData Token) False (Tele n)
  telescope ns acc =
    (do
        b <- parens $ binding (t_names acc ++ ns)
        telescope ns (MkTele (S $ t_s acc) (b :: t_tele acc) (bn b :: t_names acc))
    ) <|> pure acc

  term : Vect n String -> Rule (Term n)
  term ns
    = lam ns
    <|> pi ns
    <|> type
    <|> erased
    <|> app ns
    <|> if_ ns

  if_ : Vect n String -> Rule (Term n)
  if_ ns = do
    token (Keyword "if")
    c <- term ns
    token (Keyword "then")
    t <- term ns
    token (Keyword "else")
    e <- term ns
    pure $ If_ c t e

  erased : Rule (Term n)
  erased = token Underscore *> pure Erased

export
parse : String -> Either ParseError (TT (Maybe Q) Z)
parse src = case lex src of
  Left err => Left err
  Right ts => case Text.Parser.Core.parse (term [] <* eof) ts of
    Left (Error msg []) => Left $ SyntaxError 0 0 msg
    Left (Error msg (t :: _)) => Left $ SyntaxError (line t) (col t) msg
    Right (tm, _) => Right tm
