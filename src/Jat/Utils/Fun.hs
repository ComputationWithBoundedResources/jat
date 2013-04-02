module Jat.Utils.Fun 
  (
    (|>)
  , (|>>)
  )
where

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

