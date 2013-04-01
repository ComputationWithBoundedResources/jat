module Jat.PState.Frame 
  (
    Frame (..)
  , locals
  , opstk
  , pcounter
  , elemsF
  
  , initL
  , lookupL
  , updateL
  , elemsL
  
  , elemsS
  )
where

import Jat.PState.IntDomain
import Jat.PState.AbstrValue 
import qualified Jat.Program as P
import Jat.Utils.Pretty

import Prelude hiding (lookup, init)
--import qualified Data.Sequence as S 
--import Data.Foldable (toList)
--import Data.Monoid (mappend)

type PC        = Int
data Frame i   = Frame (LocVars i) (Stk i) P.ClassId P.MethodId PC deriving Show

locals :: Frame i -> LocVars i
locals (Frame loc _ _ _ _) = loc

pcounter :: Frame i -> PC
pcounter (Frame _ _ _ _ pc) = pc

opstk :: Frame i -> Stk i
opstk (Frame _ stk _ _ _) = stk

elemsF :: Frame i -> [AbstrValue i]
elemsF frm = locals frm ++ opstk frm

type LocVars i = [AbstrValue i]

initL :: [AbstrValue i] -> Int -> LocVars i
initL vs n = vs ++ replicate n Unit

elemsL :: LocVars i -> [AbstrValue i]
elemsL = id

lookupL :: (IntDomain i) =>  Int -> LocVars i -> AbstrValue i
lookupL i ls = lookupL' i ls
  where
    lookupL' _ []    = error $ "Jat.PState.Frame.lookupL: invalid index." ++ show i
    lookupL' 0 (f:_) = f
    lookupL' j (_:fs)= lookupL' (j-1) fs

updateL :: Int -> AbstrValue i -> LocVars i -> LocVars i
updateL i v vs = take i vs ++ v : drop (i+1) vs

type Stk i     = [AbstrValue i]

elemsS :: Stk i -> [AbstrValue i]
elemsS = id
--
--mapValuesF :: (AbstrValue i -> AbstrValue i) -> Frame i -> Frame i
--mapValuesF f (Frame(loc,stk,cn,mn,pc)) = Frame(mapValuesL f loc, mapValuesS f stk, cn, mn, pc)

--elemsF :: Frame i -> [AbstrValue i]
--elemsF (Frame(loc,stk,_,_,_)) = elemsL loc ++ elemsS stk

--lookupF :: [Frame i] -> Int -> Frame i
--lookupF fs i = lookupF' fs i
  --where
    --lookupF' [] j    = error $ "invalid index" ++ show i
    --lookupF' (f:_) 0  = f
    --lookupF'(_:fs) j = lookupF' fs (j-1)



--type LocVars i = S.Seq (AbstrValue i)
--type LocVars i = [AbstrValue i]





--mapValuesL :: (AbstrValue i -> AbstrValue i) -> LocVars i -> LocVars i
--mapValuesL = fmap

--type OpStk i   = [(AbstrValue i, Path)]

--emptyS :: OpStk i
--emptyS = []

--mapValuesS :: (AbstrValue i -> AbstrValue i) -> OpStk i -> OpStk i
--mapValuesS f = map (\(v,p) -> (f v,p))



--data Root = RStk Int Int | RLoc Int Int deriving (Eq,Show)
--data Path = Path (Root, [(P.ClassId, P.FieldId)]) | Empty deriving (Eq,Show)

--(-->) :: (P.ClassId, P.FieldId) -> Path -> Path
--k --> (Path (r, ks)) = Path (r, ks++[k])
--_ --> Empty          = error "Jat.State.Path: invalid composing of path"

instance (Pretty i) => Pretty (Frame i) where
  pretty (Frame loc stk cn mn pc) = text (show pc) `sepx` pretty cn `sepx` pretty mn <$> prettyLoc `sepx` prettyStk
    where
      sepx d f  = d <+> text "|" <+> f
      prettyLoc = encloseSep lbracket rbracket comma (map pretty $ elemsL loc)
      prettyStk = encloseSep lbracket rbracket comma (map pretty $ elemsS stk)
