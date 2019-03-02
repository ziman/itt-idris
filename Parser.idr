module Parser

import TT
import Text.Lexer
import Text.Parser
import Data.Vect

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

public export
data ParseError : Type where
  OtherError : String -> ParseError
  LexError : Int -> Int -> String -> ParseError
  SyntaxError : Int -> Int -> String -> ParseError

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

    tokens : TokenMap Token
    tokens = 
      [ (is '(',       const ParL)
      , (is ')',       const ParR)
      , (ident,        Ident)
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

term : Vect n String -> Rule (Term n)
term ns = ?rhs

export
parse : String -> Either ParseError (TT (Maybe Q) Z)
parse src = case lex src of
  Left err => Left err
  Right ts => case parse (term []) ts of
    Left (Error msg []) => Left $ SyntaxError 0 0 msg
    Left (Error msg (t :: _)) => Left $ SyntaxError (line t) (col t) msg
    Right (term, _) => Right term
