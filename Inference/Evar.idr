module Evar

import Lens
import public TT
import Control.Monad.State

%default total

public export
data ENum = EN Int

export
Eq ENum where
  (==) (EN x) (EN y) = x == y

export
Ord ENum where
  compare (EN x) (EN y) = compare x y

export
Show ENum where
  show (EN x) = show x

public export
data Evar = QQ Q | EV ENum

export
Show Evar where
  show (QQ q) = show q
  show (EV i) = show i

export
ShowQ Evar where
  showCol (QQ q) = ":" ++ show q
  showCol (EV i) = ":" ++ show i

  showApp (QQ q) = " -" ++ show q ++ "- "
  showApp (EV i) = " -" ++ show i ++ "- "

export
Eq Evar where
  (==) (QQ q) (QQ q') = q == q'
  (==) (EV i) (EV i') = i == i'
  (==) _ _ = False

export
Ord Evar where
  compare (QQ _) (EV _) = LT
  compare (EV _) (QQ _) = GT
  compare (QQ q) (QQ q') = compare q q'
  compare (EV i) (EV i') = compare i i'

export
evarify : TT (Maybe Q) n -> TT Evar n
evarify tm = evalState (ttQ f tm) 0
  where
    f : Maybe Q -> State Int Evar
    f (Just q) = pure $ QQ q
    f Nothing = do
      i <- get
      put (i+1)
      pure $ EV (EN i)
