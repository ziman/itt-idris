module Core.Quantity

import Utils.Misc
import public Utils.OrdSemiring

%default total
%undotted_record_projections off

export
xDEBUG : Bool
xDEBUG = False

public export
interface ShowQ q where
  showCol : q -> String
  showApp : q -> String

public export
data Q = I | E | L | R

export
Show Q where
  show I = "I"
  show E = "E"
  show L = "L"
  show R = "R"

export
super : String -> String
super = pack . map sup . unpack
  where
    sup : Char -> Char
    sup '0' = '⁰'
    sup '1' = '¹'
    sup '2' = '²'
    sup '3' = '³'
    sup '4' = '⁴'
    sup '5' = '⁵'
    sup '6' = '⁶'
    sup '7' = '⁷'
    sup '8' = '⁸'
    sup '9' = '⁹'
    sup 'I' = 'ᴵ'
    sup 'E' = 'ᴱ'
    sup 'L' = 'ᴸ'
    sup 'R' = 'ᴿ'
    sup c = c

export
showSup : Show a => a -> String
showSup = super . show

export
ShowQ () where
  showCol () = ":"
  showApp () = " "

export
ShowQ Q where
  showCol q =
    if xDEBUG
      then ":" ++ showSup q
      else ":" ++ show q

  showApp q =
    if xDEBUG
      then " " ++ showSup q ++ " "
      else " "

export
ShowQ (Maybe Q) where
  showCol Nothing = ":"
  showCol (Just q) = showCol q

  showApp Nothing = " "
  showApp (Just q) = showApp q

qToInt : Q -> Int
qToInt I = 0
qToInt E = 1
qToInt L = 2
qToInt R = 3

export
Eq Q where
  (==) = eqBy qToInt

export
Ord Q where
  compare = compareBy qToInt

export
OrdSemiring Q where
  semi0 = I
  semi1 = L
  top = R

  (.+.) p q = case (p, q) of
    (I, q) => q
    (q, I) => q
    (R, q) => R
    (q, R) => R
    (E, L) => L
    (L, E) => L
    (E, E) => E
    (L, L) => R  -- important!

  (.*.) p q = case (p, q) of
    (I, q) => I
    (q, I) => I
    (L, q) => q
    (q, L) => q
    (E, E) => E
    (E, R) => E
    (R, E) => E
    (R, R) => R

  -- this is dodgy
  -- is L .\/. R still R in a non-affine system?
  -- i suspect that the rules will have to be reformulated without the use of .\/.
  (.\/.) p q = case (p, q) of
    (I, q) => q
    (q, I) => q
    (R, q) => R
    (q, R) => R
    (E, L) => L
    (L, E) => L
    (E, E) => E
    (L, L) => L

  -- can we use a q-bound value p times?
  (.<=.) p q = case (p, q) of
    (I, I) => True
    (I, E) => True
    (E, E) => True
    (L, L) => True
    (_, R) => True
    _ => False

export
isBinderUsageOk : (bndQ : Q) -> (usageQ : Q) -> Bool
isBinderUsageOk I I = True
isBinderUsageOk E I = True
isBinderUsageOk E E = True
isBinderUsageOk L L = True
isBinderUsageOk R _ = True
isBinderUsageOk _ _ = False
