module Transformation.PruneClauses

import Data.Vect
import Data.List
import public Core.Globals

%default total
%undotted_record_projections off

mutual
  prunePat : Globals Q -> Pat Q n -> Bool
  prunePat gs (PV _) = False
  prunePat gs (PCtorApp (Checked cn) args) =
    case .binding.qv <$> lookup cn gs of
      Just I => True
      Just E => True
      _ => prunePatArgs gs args
  prunePat gs (PCtorApp (Forced _) args) = prunePatArgs gs args
  prunePat gs (PForced _) = False
  prunePat gs PWildcard = False

  prunePatArgs : Globals Q -> List (Q, Pat Q n) -> Bool
  prunePatArgs gs [] = False
  prunePatArgs gs ((q, arg) :: args) =
    prunePat gs arg || prunePatArgs gs args

pruneClause : Globals Q -> Clause Q argn -> List (Clause Q argn)
pruneClause gs c@(MkClause pi lhs rhs) =
  if prunePatArgs gs (toList lhs)
    then []
    else [c]

pruneDef : Globals Q -> Definition Q -> Definition Q
pruneDef gs (MkDef b (Clauses argn cs)) =
  MkDef b $ Clauses argn (concatMap (pruneClause gs) cs)
pruneDef gs d = d

export
pruneGlobals : Globals Q -> Globals Q
pruneGlobals gs = map (pruneDef gs) gs
