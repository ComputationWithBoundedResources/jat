module Jat.Utils.Fun 
  (
    (|>)
  , (|>>)
  
  , anyIntersection
  )
where

import qualified Data.Set as S

infixl 9 |>
(|>) :: Monad m => m (Maybe a) -> m (Maybe a) -> m (Maybe a)
(|>) ma mb =  do
  a <- ma
  case a of
    Just _  -> return a
    Nothing -> mb

infixl 8 |>>
(|>>) :: Monad m => m (Maybe a) -> m a -> m a
(|>>) ma b = do
  a <- ma
  case a of
    Just c  -> return c
    Nothing -> b

anyIntersection :: Ord a => [S.Set a] -> Bool
anyIntersection sets = S.size (S.unions sets) /= sum (map S.size sets)

