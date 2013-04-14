{-# LANGUAGE MultiParamTypeClasses #-}

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
import Jat.Constraints hiding (top)

import Jat.Utils.Pretty

-- |'SimpleIntDomain' defines a simple integer domain with no refinements but constraints
data SimpleIntDomain = Integer Int | AbsInteger Int deriving (Show,Eq)

instance Atom SimpleIntDomain where
  atom (Integer i)    = IConst i
  atom (AbsInteger i) = CVar ("i_"++show i)

freshInt :: Monad m => JatM m SimpleIntDomain
freshInt = do {i<-freshVarIdx; return $ AbsInteger i} 

instance AbstrDomain SimpleIntDomain Int where
  join (Integer i) (Integer j) | i == j  = return $ Integer i
  join _ _                               = freshInt
  top                                    = freshInt
  leq (Integer i) (Integer j) | i == j   = True
  leq _ (AbsInteger _)                   = True
  leq _ _                                = False

  constant = Integer
  isConstant (Integer _) = True
  isConstant _           = False

instance IntDomain SimpleIntDomain where
  Integer i +. Integer j  = eval $ Integer (i+j)
  i +. j                  = evali i j Add
  Integer i -. Integer j  = eval $ Integer (i-j)
  i -. j                  = evali i j Sub

  Integer i ==. Integer j = eval $ Boolean (i == j)
  i ==. j                 = evalb i j Eq
  Integer i /=. Integer j = eval $ Boolean (i /= j)
  i /=. j                 = evalb i j Neq
  Integer i >=. Integer j = eval $ Boolean (i>=j)
  i >=. j                 = evalb i j Gte

instance Pretty SimpleIntDomain where
  pretty (Integer i)    = int i
  pretty (AbsInteger i) = string "i_"<> int i

eval :: Monad m => a -> JatM m (Step a b)
eval = return . topEvaluation

evali :: Monad m => SimpleIntDomain -> SimpleIntDomain -> (Constraint -> Constraint -> Constraint) -> JatM m (Step SimpleIntDomain b)
evali i j cop = do {k <- freshInt; return $ evaluation k (mkcon k cop i j)}

evalb :: Monad m => SimpleIntDomain -> SimpleIntDomain -> (Constraint -> Constraint -> Constraint) -> JatM m (Step BoolDomain b)
evalb i j cop = do {b <- freshBool; return $ evaluation b (mkcon b cop i j)}

