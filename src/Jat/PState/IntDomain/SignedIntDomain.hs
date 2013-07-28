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
import Jat.Constraints hiding (top)

import Jat.Utils.Pretty

-- |'SignedIntDomain' defines a signed integer domain. 
-- 0 is element of Pos and Neg.
data SignedIntDomain = Integer Int | Pos Int | Neg Int | AbsInteger Int deriving (Show,Eq)

instance Atom SignedIntDomain where
  atom (Integer i)    = IConst i
  atom (AbsInteger i) = CVar ('i':show i)
  atom (Pos i)        = CVar ('k':show i)
  atom (Neg i)        = CVar ('n':show i)

freshInt :: Monad m => JatM m SignedIntDomain
freshInt = do {i<-freshVarIdx; return $ AbsInteger i} 

instance AbstrDomain SignedIntDomain Int where
  join (Integer i) (Integer j) 
    | i == j           = return $ Integer i
    | i >= 0 && j >= 0 = Pos `liftM` freshVarIdx
    | i <= 0 && j <= 0 = Neg `liftM` freshVarIdx
    | otherwise        = freshInt
  join (Integer i)  (Pos _) 
    | i >= 0 = Pos `liftM` freshVarIdx
  join (Integer i)  (Neg _) 
    | i <= 0 = Neg `liftM` freshVarIdx
  join v1 v2@(Integer _) = join v2 v1
  join (Pos _)  (Pos _)                 = Pos `liftM` freshVarIdx
  join (Neg _)  (Neg _)                 = Neg `liftM` freshVarIdx
  join _ _                              = freshInt

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

  constant               = Integer
  isConstant (Integer _) = True
  isConstant _           = False

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
    | isPositive i && isPositive j = evali Pos i j Add
    | isNegative i && isNegative j = evali Neg i j Add
    | otherwise                    = evali AbsInteger i j Add
  Integer i -. Integer j = eval $ Integer (i-j)
  i -. j 
    | isNegative i && isPositive j = evali Neg i j Sub
    | isPositive i && isNegative j = evali Pos i j Sub
    | otherwise                    = evali AbsInteger i j Sub

  Integer i ==. Integer j = eval $ Boolean (i == j)
  i ==. j                 = evalb i j Eq
  Integer i /=. Integer j = eval $ Boolean (i /= j)
  i /=. j                 = evalb i j Neq
  Integer i >=. Integer j = eval $ Boolean (i>=j)
  (Pos _) >=. (Neg _)    = eval $ Boolean True
  i >=. j                 = evalb i j Gte

instance Pretty SignedIntDomain where
  pretty (Integer i)    = int i
  pretty (AbsInteger i) = char 'i'<> int i
  pretty (Pos i)        = char 'k'<> int i
  pretty (Neg i)        = char 'n'<> int i

eval :: Monad m => a -> JatM m (Step a b)
eval = return . topEvaluation

evali :: Monad m => 
  (Int -> SignedIntDomain) -> SignedIntDomain -> SignedIntDomain -> 
  (Constraint -> Constraint -> Constraint) -> JatM m (Step SignedIntDomain b)
evali si i j cop = do {k <- freshVarIdx; return $ evaluation (si k) (mkcon (si k) cop i j)}

evalb :: Monad m => 
  SignedIntDomain -> SignedIntDomain -> 
  (Constraint -> Constraint -> Constraint) -> JatM m (Step BoolDomain b)
evalb i j cop = do {b <- freshBool; return $ evaluation b (mkcon b cop i j)}


