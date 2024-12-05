module Utils.DepSortedMap

-- TODO: write split

import Decidable.Equality

namespace DecOrd
  public export
  data DecOrdOutcome : (x, y : a) -> Type where
    LT : DecOrdOutcome x y
    EQ : (0 eq : x = y) -> DecOrdOutcome x y
    GT : DecOrdOutcome x y

  public export
  interface DecOrd a where
    decCmp : (x, y : a) -> DecOrdOutcome x y

  export
  (DecOrd a, DecOrd b) => DecOrd (a,b) where
    decCmp (x,y) (x', y') with (decCmp x x', decCmp y y')
      decCmp (x,y) (x',y') | (LT, _) = LT
      decCmp (x,y) (x ,y') | (EQ Refl, LT) = LT
      decCmp (x,y) (x ,y ) | (EQ Refl, EQ Refl) = EQ Refl
      decCmp (x,y) (x ,y') | (EQ Refl, GT) = GT
      decCmp (x,y) (x',y') | (GT, _) = GT

  export
  DecOrd Nat where
    decCmp Z Z = EQ Refl
    decCmp Z (S _) = LT
    decCmp (S _) Z = GT
    decCmp (S m) (S n) with (decCmp m n)
      decCmp (S m) (S n) | LT = LT
      decCmp (S n) (S n) | EQ Refl = EQ Refl
      decCmp (S m) (S n) | GT = GT

  export
  DecOrd Int where
    decCmp x y =
      case compare x y of
        LT => LT
        EQ => EQ (believe_me $ Refl {x})
        GT => GT

  export infix 3 .<=
  export
  (.<=) : DecOrd a => a -> a -> Bool
  x .<= y = case decCmp x y of
    LT   => True
    EQ _ => True
    GT   => False

private
data Tree : Nat -> (k : Type) -> (k -> Type) -> DecOrd k -> Type where
  Leaf : (kv : k) -> v kv -> Tree Z k v o
  Branch2 : Tree n k v o -> k -> Tree n k v o -> Tree (S n) k v o
  Branch3 : Tree n k v o -> k -> Tree n k v o -> k -> Tree n k v o -> Tree (S n) k v o

branch4 :
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o ->
  Tree (S (S n)) k v o
branch4 a b c d e f g =
  Branch2 (Branch2 a b c) d (Branch2 e f g)

branch5 :
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o ->
  Tree (S (S n)) k v o
branch5 a b c d e f g h i =
  Branch2 (Branch2 a b c) d (Branch3 e f g h i)

branch6 :
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o ->
  Tree (S (S n)) k v o
branch6 a b c d e f g h i j k =
  Branch3 (Branch2 a b c) d (Branch2 e f g) h (Branch2 i j k)

branch7 :
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o -> k ->
  Tree n k v o ->
  Tree (S (S n)) k v o
branch7 a b c d e f g h i j k l m =
  Branch3 (Branch3 a b c d e) f (Branch2 g h i) j (Branch2 k l m)

merge1 : Tree n k v o -> k -> Tree (S n) k v o -> k -> Tree (S n) k v o -> Tree (S (S n)) k v o
merge1 a b (Branch2 c d e) f (Branch2 g h i) = branch5 a b c d e f g h i
merge1 a b (Branch2 c d e) f (Branch3 g h i j k) = branch6 a b c d e f g h i j k
merge1 a b (Branch3 c d e f g) h (Branch2 i j k) = branch6 a b c d e f g h i j k
merge1 a b (Branch3 c d e f g) h (Branch3 i j k l m) = branch7 a b c d e f g h i j k l m

merge2 : Tree (S n) k v o -> k -> Tree n k v o -> k -> Tree (S n) k v o -> Tree (S (S n)) k v o
merge2 (Branch2 a b c) d e f (Branch2 g h i) = branch5 a b c d e f g h i
merge2 (Branch2 a b c) d e f (Branch3 g h i j k) = branch6 a b c d e f g h i j k
merge2 (Branch3 a b c d e) f g h (Branch2 i j k) = branch6 a b c d e f g h i j k
merge2 (Branch3 a b c d e) f g h (Branch3 i j k l m) = branch7 a b c d e f g h i j k l m

merge3 : Tree (S n) k v o -> k -> Tree (S n) k v o -> k -> Tree n k v o -> Tree (S (S n)) k v o
merge3 (Branch2 a b c) d (Branch2 e f g) h i = branch5 a b c d e f g h i
merge3 (Branch2 a b c) d (Branch3 e f g h i) j k = branch6 a b c d e f g h i j k
merge3 (Branch3 a b c d e) f (Branch2 g h i) j k = branch6 a b c d e f g h i j k
merge3 (Branch3 a b c d e) f (Branch3 g h i j k) l m = branch7 a b c d e f g h i j k l m

treeLookup : DecOrd k => (kv : k) -> Tree n k v o -> Maybe (v kv)
treeLookup k (Leaf k' v) with (decCmp k k')
  treeLookup k (Leaf k  v) | EQ Refl = Just v
  treeLookup k (Leaf k' v) | _       = Nothing
treeLookup k (Branch2 t1 k' t2) =
  if k .<= k' then
    treeLookup k t1
  else
    treeLookup k t2
treeLookup k (Branch3 t1 k1 t2 k2 t3) =
  if k .<= k1 then
    treeLookup k t1
  else if k .<= k2 then
    treeLookup k t2
  else
    treeLookup k t3

treeInsertWith' : DecOrd k => (kv : k) -> (Maybe (v kv) -> v kv) -> Tree n k v o
    -> Either (Tree n k v o) (Tree n k v o, k, Tree n k v o)
treeInsertWith' k v (Leaf k' v') =
  case decCmp k k' of
    LT => Right (Leaf k (v Nothing), k, Leaf k' v')
    EQ Refl => Left (Leaf k (v $ Just v'))
    GT => Right (Leaf k' v', k', Leaf k (v Nothing))
treeInsertWith' k v (Branch2 t1 k' t2) =
  if k .<= k' then
    case treeInsertWith' k v t1 of
      Left t1' => Left (Branch2 t1' k' t2)
      Right (a, b, c) => Left (Branch3 a b c k' t2)
  else
    case treeInsertWith' k v t2 of
      Left t2' => Left (Branch2 t1 k' t2')
      Right (a, b, c) => Left (Branch3 t1 k' a b c)
treeInsertWith' k v (Branch3 t1 k1 t2 k2 t3) =
  if k .<= k1 then
    case treeInsertWith' k v t1 of
      Left t1' => Left (Branch3 t1' k1 t2 k2 t3)
      Right (a, b, c) => Right (Branch2 a b c, k1, Branch2 t2 k2 t3)
  else
    if k .<= k2 then
      case treeInsertWith' k v t2 of
        Left t2' => Left (Branch3 t1 k1 t2' k2 t3)
        Right (a, b, c) => Right (Branch2 t1 k1 a, b, Branch2 c k2 t3)
    else
      case treeInsertWith' k v t3 of
        Left t3' => Left (Branch3 t1 k1 t2 k2 t3')
        Right (a, b, c) => Right (Branch2 t1 k1 t2, k2, Branch2 a b c)

treeInsertWith : DecOrd k => (kv : k) -> (Maybe (v kv) -> v kv)
    -> Tree n k v o -> Either (Tree n k v o) (Tree (S n) k v o)
treeInsertWith k v t =
  case treeInsertWith' k v t of
    Left t' => Left t'
    Right (a, b, c) => Right (Branch2 a b c)

delType : Nat -> (k : Type) -> (v : k -> Type) -> DecOrd k -> Type
delType Z k v o = ()
delType (S n) k v o = Tree n k v o

treeDelete : DecOrd k => (n : Nat) -> k -> Tree n k v o -> Either (Tree n k v o) (delType n k v o)
treeDelete _ k (Leaf k' v) with (decCmp k k')
  treeDelete _ k (Leaf k  v) | EQ Refl = Right ()
  treeDelete _ k (Leaf k' v) | _       = Left $ Leaf k' v
treeDelete (S Z) k (Branch2 t1 k' t2) =
  if k .<= k' then
    case treeDelete Z k t1 of
      Left t1' => Left (Branch2 t1' k' t2)
      Right () => Right t2
  else
    case treeDelete Z k t2 of
      Left t2' => Left (Branch2 t1 k' t2')
      Right () => Right t1
treeDelete (S Z) k (Branch3 t1 k1 t2 k2 t3) =
  if k .<= k1 then
    case treeDelete Z k t1 of
      Left t1' => Left (Branch3 t1' k1 t2 k2 t3)
      Right () => Left (Branch2 t2 k2 t3)
  else if k .<= k2 then
    case treeDelete Z k t2 of
      Left t2' => Left (Branch3 t1 k1 t2' k2 t3)
      Right () => Left (Branch2 t1 k1 t3)
  else
    case treeDelete Z k t3 of
      Left t3' => Left (Branch3 t1 k1 t2 k2 t3')
      Right () => Left (Branch2 t1 k1 t2)
treeDelete (S (S n)) k (Branch2 t1 k' t2) =
  if k .<= k' then
    case treeDelete (S n) k t1 of
      Left t1' => Left (Branch2 t1' k' t2)
      Right t1' =>
        case t2 of
          Branch2 a b c => Right (Branch3 t1' k' a b c)
          Branch3 a b c d e => Left (branch4 t1' k' a b c d e)
  else
    case treeDelete (S n) k t2 of
      Left t2' => Left (Branch2 t1 k' t2')
      Right t2' =>
        case t1 of
          Branch2 a b c => Right (Branch3 a b c k' t2')
          Branch3 a b c d e => Left (branch4 a b c d e k' t2')
treeDelete (S (S n)) k (Branch3 t1 k1 t2 k2 t3) =
  if k .<= k1 then
    case treeDelete (S n) k t1 of
      Left t1' => Left (Branch3 t1' k1 t2 k2 t3)
      Right t1' => Left (merge1 t1' k1 t2 k2 t3)
  else if k .<= k2 then
    case treeDelete (S n) k t2 of
      Left t2' => Left (Branch3 t1 k1 t2' k2 t3)
      Right t2' => Left (merge2 t1 k1 t2' k2 t3)
  else
    case treeDelete (S n) k t3 of
      Left t3' => Left (Branch3 t1 k1 t2 k2 t3')
      Right t3' => Left (merge3 t1 k1 t2 k2 t3')

treeToList : Tree n k v o -> List (kv ** v kv)
treeToList = treeToList' (:: [])
  where
    -- explicit quantification to avoid conflation with {n} from treeToList
    treeToList' : {0 n : Nat} -> ((kv ** v kv) -> List (kv ** v kv)) -> Tree n k v o -> List (kv ** v kv)
    treeToList' cont (Leaf k v) = cont (k ** v)
    treeToList' cont (Branch2 t1 _ t2) = treeToList' (:: treeToList' cont t2) t1
    treeToList' cont (Branch3 t1 _ t2 _ t3) = treeToList' (:: treeToList' (:: treeToList' cont t3) t2) t1

export
data DepSortedMap : (k : Type) -> (k -> Type) -> Type where
  Empty : DecOrd k => DepSortedMap k v
  M : (o : DecOrd k) => (n:Nat) -> Tree n k v o -> DepSortedMap k v

export
empty : DecOrd k => DepSortedMap k v
empty = Empty

export
lookup : (kv : k) -> DepSortedMap k v -> Maybe (v kv)
lookup _ Empty = Nothing
lookup k (M _ t) = treeLookup k t


export
insertWith : (kv : k) -> (Maybe (v kv) -> v kv) -> DepSortedMap k v -> DepSortedMap k v
insertWith k v Empty = M Z (Leaf k (v Nothing))
insertWith k v (M _ t) =
  case treeInsertWith k v t of
    Left t' => (M _ t')
    Right t' => (M _ t')

export
insert : (kv : k) -> v kv -> DepSortedMap k v -> DepSortedMap k v
insert kv vkv = insertWith kv (const vkv)

export
insertFrom : Foldable f => f (kv ** v kv) -> DepSortedMap k v -> DepSortedMap k v
insertFrom kvs dsm = foldl (\m, (k ** v) => insert k v m) dsm kvs

export
delete : k -> DepSortedMap k v -> DepSortedMap k v
delete _ Empty = Empty
delete k (M Z t) =
  case treeDelete Z k t of
    Left t' => (M _ t')
    Right () => Empty
delete k (M (S n) t) =
  case treeDelete (S n) k t of
    Left t' => (M _ t')
    Right t' => (M _ t')

export
fromList : DecOrd k => List (kv ** v kv) -> DepSortedMap k v
fromList kvs = insertFrom kvs empty

export
toList : DepSortedMap k v -> List (kv ** v kv)
toList Empty = []
toList (M _ t) = treeToList t

||| Gets the keys of the map.
export
keys : DepSortedMap k v -> List k
keys = map fst . toList

export
null : DepSortedMap k v -> Bool
null Empty = True
null (M _ _) = False

treeMap : ({kv : k} -> v kv -> v' kv) -> Tree n k v o -> Tree n k v' o
treeMap f (Leaf k v) = Leaf k (f v)
treeMap f (Branch2 t1 k t2) = Branch2 (treeMap f t1) k (treeMap f t2)
treeMap f (Branch3 t1 k1 t2 k2 t3)
    = Branch3 (treeMap f t1) k1 (treeMap f t2) k2 (treeMap f t3)

treeTraverse : Applicative f => ({kv : k} -> v kv -> f (v' kv)) -> Tree n k v o -> f (Tree n k v' o)
treeTraverse f (Leaf k v) = Leaf k <$> f v
treeTraverse f (Branch2 t1 k t2) =
  Branch2
    <$> treeTraverse f t1
    <*> pure k
    <*> treeTraverse f t2
treeTraverse f (Branch3 t1 k1 t2 k2 t3) =
  Branch3
    <$> treeTraverse f t1
    <*> pure k1
    <*> treeTraverse f t2
    <*> pure k2
    <*> treeTraverse f t3

export
map : ({kv : k} -> v kv -> v' kv) -> DepSortedMap k v -> DepSortedMap k v'
map _ Empty = Empty
map f (M n t) = M _ (treeMap f t)

||| Merge two maps. When encountering duplicate keys, using a function to combine the values.
||| Uses the ordering of the first map given.
export
mergeWith : ({kv : k} -> v kv -> v kv -> v kv) -> DepSortedMap k v -> DepSortedMap k v -> DepSortedMap k v
mergeWith f x y = insertFrom inserted x where
  inserted : List (kv ** v kv)
  inserted = do
    (k ** v) <- toList y
    let v' = (maybe id f $ lookup k x) v
    pure (k ** v')

||| Left-biased merge, also keeps the ordering specified  by the left map.
export
mergeLeft : DepSortedMap k v -> DepSortedMap k v -> DepSortedMap k v
mergeLeft = mergeWith const

export
(Show k, {kv : k} -> Show (v kv)) => Show (DepSortedMap k v) where
   show m = "fromList " ++ (show $ toList m)
