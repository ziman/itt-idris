module Elab.Core

import public Core.Globals
import public Core.Quantity

import Elab.Lens
import Elab.Check
import Elab.Equality
import Utils.Pretty

import Control.Monad.State

%default total
%undotted_record_projections off

public export
data Error
  = CheckError Check.Error

export
Show Core.Error where
  show (CheckError e) = show e

export
numberMetas : Globals (Maybe Q) -> Globals (Maybe Q)
numberMetas gs = evalState (mlGlobals numberMeta gs) 0
  where
    numberMeta : (n : Nat) -> MetaNum -> State Int (TT (Maybe Q) n)
    numberMeta _ _ = do
      i <- get
      put (i+1)
      pure $ Meta (MNValue i)
