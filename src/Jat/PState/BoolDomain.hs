{-# LANGUAGE MultiParamTypeClasses #-}
-- | This module provides the abstract domain for Booleans.
module Jat.PState.BoolDomain 
  (
    BoolDomain (..)
  , (.==.)
  , (./=.)
  , (.&&.)
  , (.||.)
  , (.!)
  , freshBool
  , ifFalse 
  )
where

import Jat.JatM
import Jat.PState.Step
import Jat.PState.AbstrDomain
import Jat.Constraints hiding (top)
import qualified Jat.Constraints as C (top)
import Jat.Utils.Pretty

-- | 'BoolDomain' defines a simple domain with no refinements but constraints
-- ie. if a (concrete value) can not be inferred by an operation, the operation
-- returns a (constrained) abstract Boolean.
data BoolDomain = Boolean Bool | AbstrBoolean Int deriving (Show,Eq)

instance Atom BoolDomain where
  atom (Boolean b)      = BConst b 
  atom (AbstrBoolean i) = CVar ("b_"++show i)

instance AbstrDomain BoolDomain Bool where
  join (Boolean i) (Boolean j) | i == j  = return $ Boolean i
  join _ _                               = freshBool

  top                    = freshBool
  isTop (AbstrBoolean _) = True
  isTop _                = False

  leq (Boolean i) (Boolean j) | i == j   = True
  leq _ (AbstrBoolean _)                 = True
  leq _ _                                = False

  constant = Boolean
  isConstant (Boolean _) = True
  isConstant _           = False

-- | Returns an abstract Boolean with a fresh index.
freshBool :: Monad m => JatM m BoolDomain
freshBool = do {i<-freshVarIdx; return $ AbstrBoolean i} 

eval :: Monad m => a -> JatM m (Step a b)
eval = return . topEvaluation

evalb,evalb :: Monad m => BoolDomain -> BoolDomain -> (Constraint -> Constraint -> Constraint) -> JatM m (Step BoolDomain b)
evalb i j cop = do {b <- freshBool; return $ evaluation b (mkcon b cop i j)}

-- | Comparison Operation.
(.==.),(./=.) :: Monad m => BoolDomain -> BoolDomain -> JatM m (Step BoolDomain BoolDomain)
Boolean a .==. Boolean b = eval $ Boolean (a == b)
a .==. b                 = evalb a b Eq 
Boolean a ./=. Boolean b = eval $ Boolean (a /= b)
a ./=. b                 = evalb a b Neq 

-- | Binary Boolean Operation.
(.&&.),(.||.) :: Monad m => BoolDomain -> BoolDomain -> JatM m (Step BoolDomain BoolDomain)
Boolean a .&&. Boolean b = eval $ Boolean (a && b)
Boolean False .&&. _     = eval $ Boolean False
a .&&. b@(Boolean _)     = b .&&. a
a .&&. b                 = evalb a b And
Boolean a .||. Boolean b = eval $ Boolean (a || b)
Boolean True .||. _      = eval $ Boolean True
a .||. b@(Boolean _)     = b .||. a
a .||. b                 = evalb a b Or 

-- | Not Operation.
(.!) :: Monad m => BoolDomain -> JatM m (Step BoolDomain BoolDomain)
(.!) (Boolean a)        = eval $ Boolean (not a)
(.!) a@(AbstrBoolean _) = do
  j <- freshVarIdx
  let b = AbstrBoolean j
      notcon = atom b `Ass` (Not $ atom a)
  return $ evaluation b notcon


-- | Abstract Semantics for ifFalse instruction.
-- Returns a refinement if a concrete value can not be inferred.
ifFalse :: Monad m => BoolDomain -> JatM m (Step BoolDomain BoolDomain)
ifFalse (Boolean a) = return $ Evaluation (Boolean a, C.top)
ifFalse a@(AbstrBoolean _) = return $ Refinement [(Boolean False, con False), (Boolean True, con True)]
  where con b = atom a `Ass` BConst b

instance Pretty BoolDomain where
  pretty (Boolean True)   = text "TRUE"
  pretty (Boolean False)  = text "FALSE"
  pretty (AbstrBoolean i) = string "b" <> int i

