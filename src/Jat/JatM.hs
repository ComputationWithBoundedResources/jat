{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Jat.JatM
  ( 
    JatM (..)
  , evalJatM
  , initJatST
  , freshVarIdx
  , freshKey
  , withProgram
  , getProgram
  , module Control.Monad
  )
where

import Jat.Program (Program)

import Control.Monad.State.Lazy
import Control.Monad (liftM,liftM2,foldM,mapM,sequence)


newtype JatM m a = JatM (StateT JatST m a)
     deriving (Functor, Monad, MonadState JatST)

data JatST = JatST { 
    varcounter::Int 
  , keycounter::Int 
  , program::Program
  } 

initJatST :: Program -> JatST
initJatST p = JatST {
    varcounter = 0
  , keycounter = 0
  , program    = p
  }

evalJatM :: Monad m =>  JatM m a -> JatST -> m a
evalJatM (JatM a) = evalStateT a

withProgram :: Monad m => (Program -> JatM  m a) -> JatM m a
withProgram f = gets program >>= f

getProgram :: Monad m => JatM m Program
getProgram = gets program

freshKey :: Monad m => JatM m  Int 
freshKey = do
  st <- get
  let i = keycounter st
  put $ st{ keycounter=i+1 }
  return i

freshVarIdx :: Monad m => JatM m Int 
freshVarIdx = do
  st <- get
  let i = varcounter st
  put $ st{ varcounter=i+1 }
  return i

