module Elab.Core

import public Core.Globals
import public Core.Quantity
import public Elab.Lens

import Elab.Check
import Elab.Equality
import Utils.Pretty

import Control.Monad.State

%default total

public export
data Error
  = CheckError Check.Error

export
Show Core.Error where
  show (CheckError e) = show e

export
numberMetas : Globals (Maybe Q) -> Globals (Maybe Q)
numberMetas gs = evalState 0 $ mlGlobals numberMeta gs
  where
    numberMeta : (n : Nat) -> MetaNum -> State Int (TT (Maybe Q) n)
    numberMeta _ _ = do
      i <- get
      put (i+1)
      pure $ Meta (MNValue i)

export
fill : Subst (Maybe Q) -> Globals (Maybe Q) -> Globals (Maybe Q)
fill s = substMany mlGlobals s
