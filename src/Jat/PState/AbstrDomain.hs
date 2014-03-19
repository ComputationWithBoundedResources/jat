{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | This module provides the abstract domain for primitive values.
module Jat.PState.AbstrDomain 
  ( AbstrDomain (..) )
where

import Jat.JatM
import Jat.Utils.Pretty
import Data.Maybe (isJust)

-- | The 'AbstrDomain' class.
class Pretty a => AbstrDomain a b | a -> b where
  --join semi lattice
  join  :: Monad m => a -> a -> JatM m a
  top   :: Monad m => JatM m a
  isTop :: a -> Bool
  leq   :: a -> a -> Bool

  --abstract domain
  constant :: b -> a 
  fromConstant :: a -> Maybe b
  isConstant :: a -> Bool
  isConstant = isJust . fromConstant
  widening :: Monad m => a -> a -> JatM m a 
  widening = join

