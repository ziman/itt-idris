module Utils.Pretty

%access export
%default total

data Doc : Type where
  Text : String -> Doc
  Vcat : List Doc -> Doc
  Hang : Doc -> Doc -> Doc
  Indent : Doc -> Doc
  Columns : String -> List Doc -> Doc

public export
interface Pretty ctx a where
  pretty : ctx -> a -> Doc

Semigroup Doc where
  (<+>) = Hang

Monoid Doc where
  neutral = Text ""

text : String -> Doc
text = Text

int : Int -> Doc
int = text . show

show : Show a => a -> Doc
show = Text . show

infixr 2 $$
($$) : Doc -> Doc -> Doc
($$) (Vcat xs) (Vcat ys) = Vcat (xs ++ ys)
($$) x (Vcat ys) = Vcat (x :: ys)
($$) (Vcat xs) y = Vcat (xs ++ [y])
($$) x y = Vcat [x,y]

vcat : List Doc -> Doc
vcat = Vcat

punctuate : Doc -> List Doc -> Doc
punctuate sep = concat . intersperse sep

hsep : List Doc -> Doc
hsep = punctuate (text " ")

infixl 6 <++>
(<++>) : Doc -> Doc -> Doc
(<++>) x y = x <+> text " " <+> y

indent : Doc -> Doc
indent = Indent

parens : Doc -> Doc
parens d = text "(" <+> d <+> text ")"

columns : String -> List Doc -> Doc
columns = Columns

data CN = CL Nat | CR Nat | CE

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

render : String -> Doc -> String
render ind = concat . intersperse "\n" . render' ind
