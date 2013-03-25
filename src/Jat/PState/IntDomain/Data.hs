{-# LANGUAGE FlexibleContexts #-}

module Jat.PState.IntDomain.Data
  ( IntDomain (..) )
where

import Jat.JatM
import Jat.PState.Step
import Jat.PState.AbstrDomain 
import Jat.PState.BoolDomain 
import Jat.Utils.Pretty


class (Pretty a, AbstrDomain a Int) => IntDomain a where
  (+.)  :: Monad m => a -> a -> JatM m (Step a a)
  (-.)  :: Monad m => a -> a -> JatM m (Step a a)

  (==.) :: Monad m => a -> a -> JatM m (Step BoolDomain a)
  (/=.) :: Monad m => a -> a -> JatM m (Step BoolDomain a)
  (>=.) :: Monad m => a -> a -> JatM m (Step BoolDomain a)

infix 6 +., -.
infix 4 ==., /=., >=.
 
