-- | This module defines a single frame consisting of local variables, operand
-- stack, class name, method name and program counter.
module Jat.PState.Frame 
  (
    Frame (..)
  , locals
  , opstk
  , pcounter
  , elemsF
  , mapValuesF
  
  , initL
  , lookupL
  , updateL
  , elemsL
  
  , elemsS
  , lookupS
  )
where

import Jat.PState.IntDomain
import Jat.PState.AbstrValue 
import qualified Jinja.Program as P
import Jat.Utils.Pretty as PP

import Prelude hiding (lookup, init)
--import qualified Data.Sequence as S 
--import Data.Foldable (toList)
--import Data.Monoid (mappend)

type PC        = Int
-- | The Frame type.
data Frame i   = Frame (LocVars i) (Stk i) P.ClassId P.MethodId PC deriving Show

-- | Extracts local variables.
locals :: Frame i -> LocVars i
locals (Frame loc _ _ _ _) = loc

-- | Extracts program counter.
pcounter :: Frame i -> PC
pcounter (Frame _ _ _ _ pc) = pc

-- | Extracts operand stack.
opstk :: Frame i -> Stk i
opstk (Frame _ stk _ _ _) = stk

-- | Returns the elements of local variables and operand stack.
elemsF :: Frame i -> [AbstrValue i]
elemsF frm = locals frm ++ opstk frm

-- | Maps a value function over the elements.
mapValuesF :: (AbstrValue i -> AbstrValue i) -> Frame i -> Frame i
mapValuesF f (Frame loc stk cn mn pc ) = Frame (map f loc) (map f stk) cn mn pc 


type LocVars i = [AbstrValue i]

-- | Initializes local variable register with unit values.
initL :: [AbstrValue i] -> Int -> LocVars i
initL vs n = vs ++ replicate n Unit

-- | Returns the local variable register.
elemsL :: LocVars i -> [AbstrValue i]
elemsL = id

-- | Returns the nth local variable register.
-- Returns an error if n is not an index.
lookupL :: (IntDomain i) =>  Int -> LocVars i -> AbstrValue i
lookupL i ls = lookupL' i ls
  where
    lookupL' _ []    = error $ "Jat.PState.Frame.lookupL: invalid index." ++ show i
    lookupL' 0 (f:_) = f
    lookupL' j (_:fs)= lookupL' (j-1) fs

-- | Updates nth local variable register.
updateL :: Int -> AbstrValue i -> LocVars i -> LocVars i
updateL i v vs = take i vs ++ v : drop (i+1) vs


type Stk i     = [AbstrValue i]

-- | Returns the elements of the operand stack.
elemsS :: Stk i -> [AbstrValue i]
elemsS = id

-- | Returns the nth register of the operand stack.
-- Returns an error if n is not an index.
lookupS :: (IntDomain i) =>  Int -> Stk i -> AbstrValue i
lookupS i ls = lookupS' i ls
  where
    lookupS' _ []    = error $ "Jat.PState.Frame.lookupS: invalid index." ++ show i
    lookupS' 0 (f:_) = f
    lookupS' j (_:fs)= lookupS' (j-1) fs


instance (Pretty i) => Pretty (Frame i) where
  pretty (Frame loc stk cn mn pc) = text (show pc) `sepx` pretty cn `sepx` pretty mn PP.<$> prettyLoc `sepx` prettyStk
    where
      sepx d f  = d <+> text "|" <+> f
      prettyLoc = encloseSep lbracket rbracket comma (map pretty $ elemsL loc)
      prettyStk = encloseSep lbracket rbracket comma (map pretty $ elemsS stk)

