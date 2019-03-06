module Parser

import TT
import Text.Lexer
import Text.Parser
import Data.Vect

%default total

data Token
  = Ident String
  | ParL
  | ParR
  | Lam
  | Arrow
  | Dot
  | Space
  | Comment
  | Colon (Maybe Q)
  | Keyword String

Eq Token where
  (==) x y = case (x, y) of
    (Ident x, Ident y) => x == y
    (ParL, ParL) => True
    (ParR, ParR) => True
    (Lam, Lam) => True
    (Arrow, Arrow) => True
    (Dot, Dot) => True
    (Space, Space) => True
    (Comment, Comment) => True
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
    ident = some $ pred (\x => isAlpha x || isDigit x || x == '_')

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
          [ "Type", "where", "data", "case", "of", "with"
          , "let", "in"
          ]

    tokens : TokenMap Token
    tokens = 
      [ (is '(',       const ParL)
      , (is ')',       const ParR)
      , (ident,        kwdOrIdent)
      , (is '\\',      const Lam)
      , (exact "->",   const Arrow)
      , (is '.',       const Dot)
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

var : Vect n String -> Rule (Term n)
var ns = terminal $ \t => case tok t of
  Ident n => case lookupName n ns of
    Just i => Just $ V i
    Nothing => Nothing
  _ => Nothing

ident : Rule String
ident = terminal $ \t => case tok t of
  Ident n => Just n
  _ => Nothing

colon : Rule (Maybe Q)
colon = terminal $ \t => case tok t of
  Colon mq => Just mq
  _ => Nothing

mutual
  def : Vect n String -> Rule (Def (Maybe Q) n)
  def ns = D <$> ident <*> colon <*> term ns

  lam : Vect n String -> Rule (Term n)
  lam ns = do
    token Lam
    commit
    d <- def ns
    token Dot
    rhs <- term (defName d :: ns)
    pure $ Bind Lam d rhs

  pi : Vect n String -> Rule (Term n)
  pi ns = do
    token ParL
    d <- def ns
    token ParR
    token Arrow
    commit
    rhs <- term (defName d :: ns)
    pure $ Bind Pi d rhs

  atom : Vect n String -> Rule (Term n)
  atom ns = var ns <|> do { token ParL; tm <- term ns; token ParR; pure tm }

  -- includes nullary applications (= variables)
  app : Vect n String -> Rule (Term n)
  app ns = do
    head <- atom ns
    commit
    args <- many (atom ns)
    pure $ foldl (App Nothing) head args

  term : Vect n String -> Rule (Term n)
  term ns = lam ns <|> pi ns <|> type <|> app ns

export
parse : String -> Either ParseError (TT (Maybe Q) Z)
parse src = case lex src of
  Left err => Left err
  Right ts => case parse (term []) ts of
    Left (Error msg []) => Left $ SyntaxError 0 0 msg
    Left (Error msg (t :: _)) => Left $ SyntaxError (line t) (col t) msg
    Right (term, _) => Right term
