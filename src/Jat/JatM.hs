{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- | This module provides the Jat monad providing access to the current
-- 'Program' and counters.
module Jat.JatM
  ( 
    JatM (..)
  , Jat
  , initJat
  , evalJat
  , getProgram
  , freshVarIdx
  , freshKey
  , module Control.Monad
  )
where

import Jinja.Program (Program)

import Control.Monad.State.Lazy
import Control.Monad (liftM,liftM2,foldM,mapM,sequence)
import Control.Monad.Identity


-- | The Jat monad.
newtype JatM m a = JatM (StateT JatST m a)
     deriving (Functor, Monad, MonadIO, MonadState JatST)

-- | The Jat monad with base Idenitity.
type Jat a = JatM Identity a

data JatST = JatST { 
    varcounter::Int 
  , keycounter::Int 
  , program::Program
  } 

-- | Sets the 'Program' and resets the counters.
initJat :: Program -> JatST
initJat p = JatST {
    varcounter = 0
  , keycounter = 0
  , program    = p
  }

-- | Evaluates the monad.
evalJat :: Monad m =>  JatM m a -> JatST -> m a
evalJat (JatM a) = evalStateT a

--withProgram :: Monad m => (Program -> JatM  m a) -> JatM m a
--withProgram f = gets program >>= f

-- | Returns the initialised 'Program'.
getProgram :: Monad m => JatM m Program
getProgram = gets program

-- | Returns a fresh key from the node counter.
freshKey :: Monad m => JatM m  Int 
freshKey = do
  st <- get
  let i = keycounter st
  put $ st{ keycounter=i+1 }
  return i

-- | Returns a fresh key from the variable counter.
freshVarIdx :: Monad m => JatM m Int 
freshVarIdx = do
  st <- get
  let i = varcounter st
  put $ st{ varcounter=i+1 }
  return i

