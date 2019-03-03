module Pretty

%access export
%default total

data Doc : Type where
  Text : String -> Doc
  Hcat : List Doc -> Doc
  Hang : Doc -> Doc -> Doc

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
    render' ind (Hcat ls) = concatMap (render' ind) ls
    render' ind (Hang x y) = hang ind (render' ind x) (render' ind y)
