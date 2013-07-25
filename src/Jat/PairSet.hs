{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}

module Jat.PairSet 
  (
    Pair
  , unview
  , view
  , PairSet

  , map
  , rename
  , renameWithLookup
  , fold
  , filter
  , elems
  , fromList

  , member
  , notMember
  , empty
  , singleton
  , insert
  , insert'
  {-, inserts-}
  , delete
  , delete'
  {-, deletes'-}
  , union
  , difference
  , intersection
  , isSubsetOf
  {-, restrict-}
  {-, rename-}
  , pairsWith
  , closure
  )
where


import Prelude hiding (map,filter)
import qualified Data.List as L (map)
import qualified Data.Set as S
import Data.Maybe (fromMaybe)

newtype PairSet e = Set (S.Set (e,e)) deriving (Eq,Ord)

class Ord e => Pair p e | p -> e where
  unview :: p -> (e,e)
  view   :: (e,e)  -> p

order :: Ord a => (a,a) -> (a,a)
order (a,b)
  | a <= b    = (a,b)
  | otherwise = (b,a)

mkPair :: Pair p e => p -> (e,e)
mkPair = order . unview

-- only correct if f does not take ordering into account
map :: Pair p e => (p -> p) -> PairSet e -> PairSet e
map f (Set es) =  Set $ k `S.map` es
  where k = unview . f . view

fold :: Pair p e => (p -> b -> b) -> b -> PairSet e -> b
fold f b (Set es) = S.fold (f . view) b es

filter :: Pair p e => (p -> Bool) -> PairSet e -> PairSet e
filter f (Set es) = Set $ S.filter (f . view) es

rename :: Ord e => (e -> e) -> PairSet e -> PairSet e
rename f (Set es) = Set $ k `S.map` es
  where k (e1,e2) = order (f e1, f e2)

renameWithLookup :: Ord e => (e -> Maybe e) -> PairSet e -> PairSet e
renameWithLookup f (Set es) = Set $ k `S.map` es
  where 
    k (e1,e2) = order (g e1, g e2)
    g e       = e `fromMaybe` f e

member :: Pair p e => p -> PairSet e -> Bool
member p (Set es) = mkPair p `S.member` es

notMember :: Pair p e => p -> PairSet e -> Bool
notMember p = not . member p

empty :: PairSet e
empty = Set S.empty

singleton :: Pair p e => p -> PairSet e
singleton = Set . S.singleton . mkPair

insert :: Pair p e => p -> PairSet e -> PairSet e
insert p (Set es) = Set $ mkPair p `S.insert` es

insert' :: Ord e => e -> PairSet e -> PairSet e
insert' e (Set es) = Set $ (e,e) `S.insert` es

delete :: Pair p e => p -> PairSet e -> PairSet e
delete p (Set es) = Set $ mkPair p `S.insert` es

delete' :: Ord e => e -> PairSet e -> PairSet e
delete' e (Set es) = Set $ S.filter k es
  where k (e1,e2) = e /= e1 && e /= e2

union :: Ord e => PairSet e -> PairSet e -> PairSet e
union (Set es1) (Set es2) = Set $ es1 `S.union` es2

difference :: Ord e => PairSet e -> PairSet e -> PairSet e
difference (Set es1) (Set es2) = Set $ es1 `S.difference` es2

intersection :: Ord e => PairSet e -> PairSet e -> PairSet e
intersection (Set es1) (Set es2) = Set $ es1 `S.intersection` es2

isSubsetOf :: Ord e => PairSet e -> PairSet e -> Bool
isSubsetOf (Set es1) (Set es2) = es1 `S.isSubsetOf` es2

elems :: Pair p e => PairSet e -> [p]
elems (Set es) = L.map view (S.elems es)

fromList :: Pair p e => [p] -> PairSet e
fromList = Set . S.fromList . L.map mkPair

pairsWith :: Ord e => e -> PairSet e -> [e]
pairsWith e (Set es) = S.elems . S.fromList $ S.foldl k [] es
  where
    k as (c,d)
      | e == c = d:as
      | e == d = c:as
      | otherwise = as

closure :: Ord e => [e] -> PairSet e -> PairSet e
closure as ps = ps `union` closure'
  where 
    vs       = concatMap (`pairsWith` ps) as
    closure' = Set $ S.fromList [ order (v1,v2) | v1 <- vs, v2 <- vs]

