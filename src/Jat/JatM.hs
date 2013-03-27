{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Jat.JatM
  ( 
    JatM (..)
  , Jat
  , initJat
  , evalJat
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
import Control.Monad.Identity


newtype JatM m a = JatM (StateT JatST m a)
     deriving (Functor, Monad, MonadIO, MonadState JatST)

type Jat a = JatM Identity a

type JatIO a = JatM IO a

data JatST = JatST { 
    varcounter::Int 
  , keycounter::Int 
  , program::Program
  } 

initJat :: Program -> JatST
initJat p = JatST {
    varcounter = 0
  , keycounter = 0
  , program    = p
  }

evalJat :: Monad m =>  JatM m a -> JatST -> m a
evalJat (JatM a) = evalStateT a


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

