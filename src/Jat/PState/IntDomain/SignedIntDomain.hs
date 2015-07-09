{-# LANGUAGE MultiParamTypeClasses #-}

-- | This module provides an instance for 'IntDomain'.
module Jat.PState.IntDomain.SignedIntDomain
  (
    SignedIntDomain
  )
where

import Jat.JatM
import Jat.PState.Step
import Jat.PState.AbstrDomain
import Jat.PState.BoolDomain
import Jat.PState.IntDomain.Data
import qualified Jat.Constraints as PA

import Jat.Utils.Pretty

-- |'SignedIntDomain' defines a signed integer domain. 
-- 0 is element of Pos and Neg.
data SignedIntDomain = Integer Int | Pos Int | Neg Int | AbsInteger Int deriving (Show,Eq,Ord)

freshInt :: Monad m => JatM m SignedIntDomain
freshInt = do {i<-freshVarIdx; return $ AbsInteger i} 

instance AbstrDomain SignedIntDomain Int where
  lub (Integer i) (Integer j) 
    | i == j           = return $ Integer i
    | i >= 0 && j >= 0 = Pos `liftM` freshVarIdx
    | i <= 0 && j <= 0 = Neg `liftM` freshVarIdx
    | otherwise        = freshInt
  lub (Integer i)  (Pos _) 
    | i >= 0 = Pos `liftM` freshVarIdx
  lub (Integer i)  (Neg _) 
    | i <= 0 = Neg `liftM` freshVarIdx
  lub v1 v2@(Integer _) = lub v2 v1
  lub (Pos _)  (Pos _)                 = Pos `liftM` freshVarIdx
  lub (Neg _)  (Neg _)                 = Neg `liftM` freshVarIdx
  lub _ _                              = freshInt

  top                  = freshInt
  isTop (AbsInteger _) = True
  isTop _              = False

  leq (Integer i) (Integer j) | i == j  = True
  leq (Integer i) (Pos _) | i >= 0  = True
  leq (Integer i) (Neg _) | i <= 0  = True
  leq (Pos _)     (Pos _)          = True
  leq (Neg _)     (Neg _)          = True
  leq _ (AbsInteger _)                  = True
  leq _ _                               = False

  atom (Integer i)         = PA.int i
  atom (AbsInteger i)      = PA.ivar "" i
  atom (Pos i)             = PA.ivar "pos" i
  atom (Neg i)             = PA.ivar "neg" i
  constant                 = Integer
  fromConstant (Integer i) = Just i
  fromConstant _           = Nothing

isPositive :: SignedIntDomain -> Bool
isPositive (Integer i) = i >= 0
isPositive (Pos _)     = True
isPositive _           = False

isNegative :: SignedIntDomain -> Bool
isNegative (Integer i) = i <= 0
isNegative (Neg _)     = True
isNegative _           = False

instance IntDomain SignedIntDomain where
  Integer i +. Integer j = eval $ Integer (i+j)
  i +. j 
    | isPositive i && isPositive j = evali PA.add Pos i j
    | isNegative i && isNegative j = evali PA.add Neg i j
    | otherwise                    = evali PA.add AbsInteger i j
  Integer i -. Integer j = eval $ Integer (i-j)
  i -. j 
    | isNegative i && isPositive j = evali PA.sub Neg i j
    | isPositive i && isNegative j = evali PA.sub Pos i j
    | otherwise                    = evali PA.sub AbsInteger i j

  Integer i ==. Integer j = eval $ Boolean (i == j)
  i ==. j                 = evalb PA.eq i j
  Integer i /=. Integer j = eval $ Boolean (i /= j)
  i /=. j                 = evalb PA.neq i j
  Integer i >=. Integer j = eval $ Boolean (i>=j)
  (Pos _) >=. (Neg _)    = eval $ Boolean True
  i >=. j                 = evalb PA.gte i j

instance Pretty SignedIntDomain where
  pretty (Integer i)    = int i
  pretty (AbsInteger i) = char 'i'<> int i
  pretty (Pos i)        = char 'k'<> int i
  pretty (Neg i)        = char 'n'<> int i

eval :: Monad m => a -> JatM m (Step a b)
eval = return . topEvaluation

evali :: Monad m => 
  (PA.PATerm -> PA.PATerm -> PA.PATerm)
  -> (Int -> SignedIntDomain) -> SignedIntDomain -> SignedIntDomain
  -> JatM m (Step SignedIntDomain b)
evali f si i j = do {k <- freshVarIdx; return $ evaluation (si k) (mkcon (si k) f i j)}

evalb :: Monad m => 
  (PA.PATerm -> PA.PATerm -> PA.PATerm)
  -> SignedIntDomain -> SignedIntDomain
  -> JatM m (Step BoolDomain b)
evalb f i j = do {b <- freshBool; return $ evaluation b (mkcon b f i j)}


