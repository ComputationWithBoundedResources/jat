module Jat.PairSet 
  (
    PairSet

  , map
  , fold
  , filter
  , elems
  , fromList

  , empty
  , insert
  , insert'
  , inserts
  , member
  , delete
  , delete'
  , deletes'
  , union
  , restrict
  , rename
  , closure
  )
where


import Prelude hiding (map,filter)
import qualified Data.Set as S
import Data.Maybe (fromMaybe)

newtype Pair a = Pair (a,a) deriving (Eq,Ord)

instance Show a => Show (Pair a) where
  show (Pair(a,b)) = '<' :show a ++ ',' :show b ++ ">"

order :: Ord a => (a,a) -> (a,a)
order (a,b)
  | a <= b    = (a,b)
  | otherwise = (b,a)

mkPair :: Ord a => (a,a) -> Pair a
mkPair a = Pair $ order a

newtype PairSet a = Set (S.Set (Pair a)) deriving (Eq,Ord)

instance Show a => Show (PairSet a) where
  show (Set ps) = show ps

map :: (Ord a, Ord b) => (a -> b) -> PairSet a -> PairSet b
map f (Set ps) = Set $ S.map k ps
  where k (Pair (a,b)) = mkPair (f a, f b)

fold :: (a -> Pair b -> a) -> a -> PairSet b -> a
fold f a (Set ps) = S.foldl f a ps

filter :: Ord a => ((a,a) -> Bool) -> PairSet a -> PairSet a
filter f (Set ps) = Set $ S.filter (\(Pair a)-> f a) ps

empty :: PairSet a
empty = Set S.empty 

fromList :: Ord a => [(a,a)] -> PairSet a
fromList = Set . foldl (\s p -> mkPair p `S.insert` s) S.empty

elems :: PairSet a -> [(a,a)]
elems (Set ps) = S.foldr (\(Pair p) -> (p:)) [] ps

insert :: Ord a => (a,a) -> PairSet a -> PairSet a
insert p (Set ps) = Set $ mkPair p `S.insert` ps

insert' :: Ord a => a -> PairSet a -> PairSet a
insert' a = insert (a,a)

inserts :: Ord a => [(a,a)] -> PairSet a -> PairSet a
inserts ns ps = foldl (flip insert) ps ns

union :: Ord a => PairSet a -> PairSet a -> PairSet a
union (Set ps1) (Set ps2) = Set $ ps1 `S.union` ps2

member :: Ord a => (a,a) -> PairSet a -> Bool
member p (Set ps) = mkPair p `S.member` ps

delete :: Ord a => (a,a) -> PairSet a -> PairSet a
delete p (Set ps) = Set $ mkPair p `S.delete` ps

delete' :: Ord a => a -> PairSet a -> PairSet a
delete' a (Set ps) = Set $ S.filter (\(Pair(b,c)) -> a /= b && a /= c) ps

deletes' :: Ord a => [a] -> PairSet a -> PairSet a
deletes' as ps = foldl (flip delete') ps as

pairsWith :: Ord a => a -> PairSet a -> [a]
pairsWith a (Set ps) = S.elems . S.fromList $ S.foldl k [] ps
  where
    k as (Pair(c,d))
      | a == c = d:as
      | a == d = c:as
      | otherwise = as

closure :: Ord a => [a] -> PairSet a -> PairSet a
closure as ps = ps `union` closure'
  where 
    vs       = concatMap (`pairsWith` ps) as
    closure' = Set $ S.fromList [ mkPair (v1,v2) | v1 <- vs, v2 <- vs]

restrict :: Ord a => [a] -> PairSet a -> PairSet a
restrict as (Set ps) = Set $ S.filter k ps
  where k (Pair (b,c)) = b `elem` as || c `elem` as

rename :: Ord a => [(a,a)] -> PairSet a -> PairSet a
rename as ps = renameElem `map` ps
  where renameElem b = b `fromMaybe` lookup b as



