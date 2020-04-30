module Utils.Pretty

import Data.List

%default total

export
data Doc : Type where
  Text : String -> Doc
  Vcat : List Doc -> Doc
  Hang : Doc -> Doc -> Doc
  Indent : Doc -> Doc
  Columns : String -> List Doc -> Doc

public export
interface Pretty ctx a where
  pretty : ctx -> a -> Doc

export
Semigroup Doc where
  (<+>) = Hang

export
Monoid Doc where
  neutral = Text ""

export
text : String -> Doc
text = Text

export
show : Show a => a -> Doc
show = Text . show

infixr 2 $$
export
($$) : Doc -> Doc -> Doc
($$) (Vcat xs) (Vcat ys) = Vcat (xs ++ ys)
($$) x (Vcat ys) = Vcat (x :: ys)
($$) (Vcat xs) y = Vcat (xs ++ [y])
($$) x y = Vcat [x,y]

export
vcat : List Doc -> Doc
vcat = Vcat

export
punctuate : Doc -> List Doc -> Doc
punctuate sep = concat . intersperse sep

export
hsep : List Doc -> Doc
hsep = punctuate (text " ")

infixl 6 <++>
export
(<++>) : Doc -> Doc -> Doc
(<++>) x y = x <+> text " " <+> y

export
indent : Doc -> Doc
indent = Indent

export
indentBlock : List Doc -> Doc
indentBlock = indent . vcat

export
parens : Doc -> Doc
parens d = text "(" <+> d <+> text ")"

export
brackets : Doc -> Doc
brackets d = text "[" <+> d <+> text "]"

export
braces : Doc -> Doc
braces d = text "{" <+> d <+> text "}"

export
columns : String -> List Doc -> Doc
columns = Columns

export
data CN = CL Nat | CR Nat | CE

export
compareNat : Nat -> Nat -> CN
compareNat Z Z = CE
compareNat n Z = CR n
compareNat Z n = CL n
compareNat (S m) (S n) = compareNat m n

private
hang : String -> List String -> List String -> List String
hang ind [] ys = ys
hang ind xs [] = xs
hang ind [x] (y :: ys) = (x ++ y) :: map (ind++) ys
hang ind (x :: xs) ys = x :: hang ind xs ys

private
extendTo : Nat -> String -> String
extendTo w s = case compareNat w (length s) of
  CL _    => substr 0 w s
  CE      => s
  CR diff => s ++ pack (replicate diff ' ')

private
box : List String -> List String
box ls =
  let w = foldr (max . length) 0 ls
    in map (extendTo w) ls

private
extendRowsTo : Nat -> List String -> List String
extendRowsTo r ls = case compareNat r (length ls) of
  CL _    => take r ls  -- should never happen
  CE      => ls
  CR diff => ls ++ replicate diff ""

private
render' : String -> Doc -> List String
render' ind (Text s) = [s]
render' ind (Vcat ls) = assert_total $ concatMap (render' ind) ls  -- termination checker wat
render' ind (Hang x y) = hang ind (render' ind x) (render' ind y)
render' ind (Indent x) = map (ind++) $ render' ind x
render' ind (Columns sep ds)
    = assert_total
    $ map concat
    $ transpose
    $ intersperse sepc
    $ cols
  where
    ls : List (List String)
    ls = map (box . render' ind) ds

    rows : Nat
    rows = foldr (max . length) 0 ls

    sepc : List String
    sepc = replicate rows sep

    cols : List (List String)
    cols = map (extendRowsTo rows) ls

export
render : String -> Doc -> String
render ind = concat . intersperse "\n" . render' ind
