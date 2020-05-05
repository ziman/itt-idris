module Inference.Variance

import public Core.TT
import public Utils.Pretty
import public Inference.Evar
import public Data.SortedSet

import Core.TT.Utils

public export
record Variance where
  constructor MkV
  covariant : SortedSet ENum
  contravariant : SortedSet ENum

export
Semigroup Variance where
  MkV co contra <+> MkV co' contra' =
    MkV (co <+> co') (contra <+> contra')

export
Monoid Variance where
  neutral = MkV empty empty

export
variance : TT Evar n -> Variance
variance ty =
  let (co, contra) = getVariance ty
    in MkV (concatMap getENum co) (concatMap getENum contra)

export
Pretty () Variance where
  pretty () (MkV co contra) =
    text ("covariant: " ++ show (toList co))
    $$ text ("contravariant: " ++ show (toList contra))
