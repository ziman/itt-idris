module Core.Clause

import public Core.TT
import public Core.TT.Lens
import public Core.TT.Pretty
import public Core.Context
import public Core.Pattern

import Data.List
import Data.Vect

%default total

public export
record Clause (q : Type) (argn : Nat) where
  constructor MkClause
  {pn : Nat}
  pi : Context q pn
  lhs : Vect argn (q, Pat q pn)
  rhs : TT q pn

prettyPi : ShowQ q => Context q n -> Doc -> Doc
prettyPi [] clause = clause
prettyPi pi clause =
  text "forall" <++> pretty () pi <+> text "."
  $$ clause

export
ShowQ q => Pretty Name (Clause q argn) where
  pretty fn c =
    prettyPi c.pi $
      pretty () fn
      <++> hsep (map (pretty c.pi . snd) (toList c.lhs))
      <++> text "~>"
      <++> pretty (PTT True NoParens, c.pi) c.rhs

export
clauseQ : Traversal (Clause q argn) (Clause q' argn) q q'
clauseQ f (MkClause pi lhs rhs) =
  [| MkClause (contextQ f pi) (traverse (qpatQ f) lhs) (ttQ f rhs) |]

public export
record RawClause (q : Type) where
  constructor MkRC
  {pn : Nat}
  pi : Context q pn
  lhs : List (q, Pat q pn)
  rhs : TT q pn

checkVect : (n : Nat) -> List a -> Maybe (Vect n a)
checkVect Z [] = Just []
checkVect (S n) (x :: xs) = (x ::) <$> checkVect n xs
checkVect _ _ = Nothing

checkClause : (argn : Nat) -> RawClause q -> Maybe (Clause q argn)
checkClause argn rc =
  checkVect argn rc.lhs <&>
    \lhs => MkClause rc.pi lhs rc.rhs

export
fromRaw : List (RawClause q) -> Maybe (argn ** List (Clause q argn))
fromRaw [] = Nothing
fromRaw (c :: cs) =
  let argn = length c.lhs
    in case traverse (checkClause argn) (c :: cs) of
      Nothing => Nothing
      Just cs' => Just (argn ** cs')
