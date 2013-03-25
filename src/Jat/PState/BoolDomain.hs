{-# LANGUAGE MultiParamTypeClasses #-}
module Jat.PState.BoolDomain 
  (
    BoolDomain (..)
  , (.==.)
  , (./=.)
  , (.&&.)
  , (.||.)
  , (.!)
  , freshBool
  , atom
  , ifFalse 
  )
where

import Jat.JatM
import Jat.PState.Step
import Jat.PState.AbstrDomain
import Jat.Constraints hiding (top)
import qualified Jat.Constraints as C (top)
import Jat.Utils.Pretty

-- | 'BoolDomain' defines a simple Domain with no refinements but constraints
data BoolDomain = Boolean Bool | AbstrBoolean Int deriving (Show,Eq)

instance Atom BoolDomain where
  atom (Boolean b)      = BConst b 
  atom (AbstrBoolean i) = CVar ("b_"++show i)

instance AbstrDomain BoolDomain Bool where
  join (Boolean i) (Boolean j) | i == j  = return $ Boolean i
  join _ _                               = freshBool
  top                                    = freshBool
  leq (Boolean i) (Boolean j) | i == j   = return True
  leq _ (AbstrBoolean _)                 = return True
  leq _ _                                = return False

  constant = Boolean

freshBool :: Monad m => JatM m BoolDomain
freshBool = do {i<-freshVarIdx; return $ AbstrBoolean i} 

eval :: Monad m => a -> JatM m (Step a b)
eval = return . topEvaluation

{-evali,evalb :: (Monad m, IntDomain i) => i -> i -> (Constraint -> Constraint -> Constraint) -> JatM m (Step BoolDomain b)-}
evalb i j cop = do {b <- freshBool; return $ evaluation b (mkcon b cop i j)}

(.==.),(./=.) :: Monad m => BoolDomain -> BoolDomain -> JatM m (Step BoolDomain BoolDomain)
Boolean a .==. Boolean b = eval $ Boolean (a == b)
a .==. b                 = evalb a b Eq 
Boolean a ./=. Boolean b = eval $ Boolean (a /= b)
a ./=. b                 = evalb a b Neq 

(.&&.),(.||.) :: Monad m => BoolDomain -> BoolDomain -> JatM m (Step BoolDomain BoolDomain)
Boolean a .&&. Boolean b = eval $ Boolean (a && b)
Boolean False .&&. _     = eval $ Boolean False
a .&&. b@(Boolean _)     = b .&&. a
a .&&. b                 = evalb a b And
Boolean a .||. Boolean b = eval $ Boolean (a || b)
Boolean True .||. _      = eval $ Boolean True
a .||. b@(Boolean _)     = b .||. a
a .||. b                 = evalb a b Or 

(.!) :: Monad m => BoolDomain -> JatM m (Step BoolDomain BoolDomain)
(.!) (Boolean a)        = eval $ Boolean (not a)
(.!) a@(AbstrBoolean _) = do
  j <- freshVarIdx
  let b = AbstrBoolean j
      notcon = atom b `Eq` (Not $ atom a)
  return $ evaluation b notcon


ifFalse :: Monad m => BoolDomain -> JatM m (Step BoolDomain BoolDomain)
ifFalse (Boolean a) = return $ Evaluation (Boolean a, C.top)
ifFalse a@(AbstrBoolean _) = return $ Refinement [(Boolean False, con False), (Boolean True, con True)]
  where con b = atom a `Eq` BConst b

instance Pretty BoolDomain where
  pretty (Boolean b) = text $ show b
  pretty (AbstrBoolean i) = string "b_" <> int i

