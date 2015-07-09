{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | This module provides the abstract domain for primitive values.
module Jat.PState.AbstrDomain 
  ( AbstrDomain (..), mkcon)
where

import Jat.JatM
import Jat.Utils.Pretty
import Jat.Constraints (PATerm, ass)

import Data.Maybe (isJust)

-- | The 'AbstrDomain' class.
class Pretty a => AbstrDomain a b | a -> b where
  --join semi lattice
  lub  :: Monad m => a -> a -> JatM m a
  top   :: Monad m => JatM m a
  isTop :: a -> Bool
  leq   :: a -> a -> Bool

  --abstract domain
  atom :: a -> PATerm
  constant :: b -> a 
  fromConstant :: a -> Maybe b
  isConstant :: a -> Bool
  isConstant = isJust . fromConstant
  widening :: Monad m => a -> a -> JatM m a 
  widening = lub

-- | Assignment constructor.
mkcon :: (AbstrDomain a b, AbstrDomain c d, AbstrDomain e f) =>
  a -> (PATerm -> PATerm -> PATerm) -> c -> e -> PATerm
mkcon i f j k = atom i `ass` (atom j `f` atom k)

