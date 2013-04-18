-- | This modules provides some common functionality.
module Jat.Utils.Fun 
  (
    (|>)
  , (|>>)
  
  , anyIntersection
  )
where

import qualified Data.Set as S

infixl 9 |>
-- | Returns the first computation if successfull, otherwise the second computation.
-- Returns 'Nothing' if all compuations are not successfull.
-- Similar to 'mplus' but performs sequential computation.
(|>) :: Monad m => m (Maybe a) -> m (Maybe a) -> m (Maybe a)
(|>) ma mb =  do
  a <- ma
  case a of
    Just _  -> return a
    Nothing -> mb

infixl 8 |>>
-- | Similar to '(|>>)' but returns a successfull computation.
(|>>) :: Monad m => m (Maybe a) -> m a -> m a
(|>>) ma b = do
  a <- ma
  case a of
    Just c  -> return c
    Nothing -> b

-- | Checks if there exists any intersection given a list of sets.
anyIntersection :: Ord a => [S.Set a] -> Bool
anyIntersection sets = S.size (S.unions sets) /= sum (map S.size sets)

