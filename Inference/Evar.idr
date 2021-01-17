module Inference.Evar

import Core.TT.Lens
import public Core.TT
import public Data.SortedMap
import public Data.SortedSet
import public Control.Monad.State

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
  showCol (QQ q) = showCol q
  showCol (EV i) =
    if xDEBUG
      then ":" ++ showSup i
      else ":" ++ show i

  showApp (QQ q) = showApp q
  showApp (EV i) =
    if xDEBUG
      then " " ++ showSup i ++ " "
      else " "

export
Pretty () Evar where
  pretty () = text . show

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
evarify : ((Maybe Q -> State Int Evar) -> a -> State Int b) -> a -> b
evarify travQ x = evalState 0 $ travQ f x
  where
    f : Maybe Q -> State Int Evar
    f (Just q) = pure $ QQ q
    f Nothing = do
      i <- get
      put (i+1)
      pure $ EV (EN i)

export
substQ : SortedMap ENum Q -> Evar -> Maybe Q
substQ vs (QQ q) = Just q
substQ vs (EV i) = SortedMap.lookup i vs <|> Just I
-- sometimes, Z3 does not return any solution for some variables
-- i assume that in such cases you can freely choose what you like
-- so we choose "I" here, by appending "<|> Just I"
-- this function thus never returns Nothing

export
getENum : Evar -> SortedSet ENum
getENum (EV i) = insert i empty
getENum (QQ _) = empty
