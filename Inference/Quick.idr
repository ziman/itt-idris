module Inference.Quick

import public Core.TT
import public Core.Globals
import public Core.Quantity
import public Inference.Evar
import public Inference.Constraint
import public Compiler.Config
import public Compiler.Monad
import public Data.SortedMap

toQuick : Evar -> Evar
toQuick (QQ L) = QQ R
toQuick ev = ev

solveQuick : Config -> Globals Evar -> Constrs -> ITT (SortedMap ENum Q)
solveQuick cfg gs cs = ?rhs

export
solve : Config -> Globals Evar -> Constrs -> ITT (SortedMap ENum Q)
solve cfg gs cs = solveQuick cfg (mapQ globalsQ toQuick gs) (mapQ constrsQ toQuick cs)
