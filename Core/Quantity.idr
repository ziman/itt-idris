module Core.Quantity

import Utils.Misc
import public Utils.OrdSemiring

%default total
%undotted_record_projections off

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
ShowQ () where
  showCol () = ":"
  showApp () = " "

export
ShowQ Q where
  showCol q = ":" ++ show q
  showApp q = " -" ++ show q ++ "- "

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
    (R, q) => q
    (q, R) => q
    (E, L) => E
    (L, E) => E
    (E, E) => E
    (L, L) => L

  (.\/.) p q = case (p, q) of
    (I, q) => q
    (q, I) => q
    (R, q) => R
    (q, R) => R
    (E, L) => L
    (L, E) => L
    (E, E) => E
    (L, L) => L

  (.<=.) p q = case (p, q) of
    (I, _) => True
    (E, E) => True
    (E, R) => True
    (L, L) => True
    (L, R) => True
    (R, R) => True
    _ => False
