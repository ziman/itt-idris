module Inference.Quick

import public Core.TT
import public Core.Quantity

-- Quick Quantities
public export
data QQ = I | E | R

export
Show QQ where
  show I = "I"
  show E = "E"
  show R = "R"

export
toQ : QQ -> Q
toQ I = I
toQ E = E
toQ R = R

export
fromQ : Q -> QQ
fromQ I = I
fromQ E = E
fromQ L = R
fromQ R = R

export
ShowQ QQ where
  showCol = showCol . toQ
  showApp = showApp . toQ


