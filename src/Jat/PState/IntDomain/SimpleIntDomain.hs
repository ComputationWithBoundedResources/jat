{-# LANGUAGE MultiParamTypeClasses #-}

-- | This module provides an instance for 'IntDomain'.
module Jat.PState.IntDomain.SimpleIntDomain 
  (
    SimpleIntDomain
  )
where

import Jat.JatM
import Jat.PState.Step
import Jat.PState.AbstrDomain
import Jat.PState.BoolDomain
import Jat.PState.IntDomain.Data
import qualified Jat.Constraints as PA

import Jat.Utils.Pretty

-- |'SimpleIntDomain' defines a simple integer domain with no refinements but constraints.
data SimpleIntDomain = Integer Int | AbsInteger Int deriving (Show,Eq,Ord)

freshInt :: Monad m => JatM m SimpleIntDomain
freshInt = do {i<-freshVarIdx; return $ AbsInteger i} 

instance AbstrDomain SimpleIntDomain Int where
  join (Integer i) (Integer j) | i == j  = return $ Integer i
  join _ _                               = freshInt

  top                  = freshInt
  isTop (AbsInteger _) = True
  isTop _              = False

  leq (Integer i) (Integer j) | i == j   = True
  leq _ (AbsInteger _)                   = True
  leq _ _                                = False

  atom (Integer i)         = PA.int i
  atom (AbsInteger i)      = PA.ivar "" i
  constant                 = Integer
  fromConstant (Integer i) = Just i
  fromConstant _           = Nothing

instance IntDomain SimpleIntDomain where
  Integer i +. Integer j  = eval $ Integer (i+j)
  i +. j                  = evali PA.add i j
  Integer i -. Integer j  = eval $ Integer (i-j)
  i -. j                  = evali PA.sub i j

  Integer i ==. Integer j = eval $ Boolean (i == j)
  i ==. j                 = evalb PA.eq i j
  Integer i /=. Integer j = eval $ Boolean (i /= j)
  i /=. j                 = evalb PA.neq i j
  Integer i >=. Integer j = eval $ Boolean (i>=j)
  i >=. j                 = evalb PA.gte i j

instance Pretty SimpleIntDomain where
  pretty (Integer i)    = int i
  pretty (AbsInteger i) = char 'i' <> int i

eval :: Monad m => a -> JatM m (Step a b)
eval = return . topEvaluation

evali :: Monad m => (PA.PATerm -> PA.PATerm -> PA.PATerm) -> SimpleIntDomain -> SimpleIntDomain -> JatM m (Step SimpleIntDomain b)
evali f i j = do {k <- freshInt; return $ evaluation k (mkcon k f i j)}

evalb :: Monad m => (PA.PATerm -> PA.PATerm -> PA.PATerm) -> SimpleIntDomain -> SimpleIntDomain -> JatM m (Step BoolDomain b)
evalb f i j = do {b <- freshBool; return $ evaluation b (mkcon b f i j)}

