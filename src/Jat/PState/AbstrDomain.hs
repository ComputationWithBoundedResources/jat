{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Jat.PState.AbstrDomain 
  ( AbstrDomain (..) )
where

import Jat.JatM
import Jat.Utils.Pretty

class Pretty a => AbstrDomain a b | a -> b where
  --join semi lattice
  join :: Monad m => a -> a -> JatM m a
  top  :: Monad m => JatM m a
  leq  :: a -> a -> Bool

  --abstract domain
  constant :: b -> a 
  widening :: Monad m => a -> a -> JatM m a 
  widening = join

