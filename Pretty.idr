module Pretty

%access export
%default total

data Doc : Type where
  Text : String -> Doc
  Vcat : List Doc -> Doc
  Hang : Doc -> Doc -> Doc
  Indent : String -> Doc -> Doc

public export
interface Pretty ctx a where
  pretty : ctx -> a -> Doc

Semigroup Doc where
  (<+>) = Hang

Monoid Doc where
  neutral = Text ""

text : String -> Doc
text = Text

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

hsep : List Doc -> Doc
hsep = concat . intersperse (text " ")

infixl 6 <++>
(<++>) : Doc -> Doc -> Doc
(<++>) x y = x <+> text " " <+> y

indent : String -> Doc -> Doc
indent = Indent

parens : Doc -> Doc
parens d = text "(" <+> d <+> text ")"

private
hang : String -> List String -> List String -> List String
hang ind [] ys = ys
hang ind xs [] = xs
hang ind [x] (y :: ys) = (x ++ y) :: map (ind++) ys
hang ind (x :: xs) ys = x :: hang ind xs ys

render : String -> Doc -> String
render ind = unlines . render' ind
  where
    render' : String -> Doc -> List String
    render' ind (Text s) = [s]
    render' ind (Vcat ls) = assert_total $ concatMap (render' ind) ls  -- termination checker wat
    render' ind (Hang x y) = hang ind (render' ind x) (render' ind y)
    render' ind (Indent ind' x) = map (ind'++) $ render' ind x
