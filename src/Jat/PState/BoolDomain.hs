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
import qualified Jat.Constraints as PA
import qualified Jat.Constraints as C (top)
import Jat.Utils.Pretty hiding (bool)

-- | 'BoolDomain' defines a simple domain with no refinements but constraints
-- ie. if a (concrete value) can not be inferred by an operation, the operation
-- returns a (constrained) abstract Boolean.
data BoolDomain = Boolean Bool | AbstrBoolean Int deriving (Show,Eq,Ord)

instance AbstrDomain BoolDomain Bool where
  join (Boolean i) (Boolean j) | i == j  = return $ Boolean i
  join _ _                               = freshBool

  top                    = freshBool
  isTop (AbstrBoolean _) = True
  isTop _                = False

  leq (Boolean i) (Boolean j) | i == j   = True
  leq _ (AbstrBoolean _)                = True
  leq _ _                               = False

  atom (Boolean b)         = PA.bool b
  atom (AbstrBoolean i)    = PA.bvar "" i
  constant                 = Boolean
  fromConstant (Boolean b) = Just b
  fromConstant _           = Nothing

-- | Returns an abstract Boolean with a fresh index.
freshBool :: Monad m => JatM m BoolDomain
freshBool = do {i<-freshVarIdx; return $ AbstrBoolean i} 

eval :: Monad m => a -> JatM m (Step a b)
eval = return . topEvaluation

evalb :: Monad m => (PA.PATerm -> PA.PATerm -> PA.PATerm) -> BoolDomain -> BoolDomain -> JatM m (Step BoolDomain b)
evalb f i j = do {b <- freshBool; return $ evaluation b (mkcon b f i j)}

-- | Comparison Operation.
(.==.),(./=.) :: Monad m => BoolDomain -> BoolDomain -> JatM m (Step BoolDomain BoolDomain)
Boolean a .==. Boolean b = eval $ Boolean (a == b)
a .==. b                 = evalb PA.eq a b
Boolean a ./=. Boolean b = eval $ Boolean (a /= b)
a ./=. b                 = evalb PA.neq a b

-- | Binary Boolean Operation.
(.&&.),(.||.) :: Monad m => BoolDomain -> BoolDomain -> JatM m (Step BoolDomain BoolDomain)
Boolean a .&&. Boolean b = eval $ Boolean (a && b)
Boolean False .&&. _     = eval $ Boolean False
a .&&. b@(Boolean _)     = b .&&. a
a .&&. b                 = evalb PA.and a b
Boolean a .||. Boolean b = eval $ Boolean (a || b)
Boolean True .||. _      = eval $ Boolean True
a .||. b@(Boolean _)     = b .||. a
a .||. b                 = evalb PA.or a b

-- | Not Operation.
(.!) :: Monad m => BoolDomain -> JatM m (Step BoolDomain BoolDomain)
(.!) (Boolean a)        = eval $ Boolean (not a)
(.!) a@(AbstrBoolean _) = do
  j <- freshVarIdx
  let b = AbstrBoolean j
      notcon = atom b `PA.ass` (PA.not $ atom a)
  return $ evaluation b notcon


-- | Abstract Semantics for ifFalse instruction.
-- Returns a refinement if a concrete value can not be inferred.
ifFalse :: Monad m => BoolDomain -> JatM m (Step BoolDomain (BoolDomain -> BoolDomain))
ifFalse (Boolean a) = return $ Evaluation (Boolean a, C.top)
ifFalse a@(AbstrBoolean _) = return $ Refinement [(sub a (Boolean False), con False), (sub a (Boolean True), con True)]
  where 
    con b = atom a `PA.ass` PA.bool b
    sub a b v = if v == a then b else v

instance Pretty BoolDomain where
  pretty (Boolean True)   = text "true"
  pretty (Boolean False)  = text "false"
  pretty (AbstrBoolean i) = char 'b' <> int i

