module Jat.PState.Frame 
  (
    Frame (..)
  --, mapValuesF
  --, elemsF
  --, lookupF

  --, LocVars
  --, initL
  , lookupL
  , updateL
  --, updateL

  --, OpStk
  --, emptyS

  --, Root (..)
  --, Path (..)
  --, (-->)
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
type LocVars i = [AbstrValue i]
type Stk i     = [AbstrValue i]
data Frame i   = Frame (LocVars i) (Stk i) P.ClassId P.MethodId PC deriving Show

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



--initL :: [AbstrValue i] -> Int -> LocVars i
--initL vs n = S.fromList vs `mappend` S.replicate n Unit
--initL vs n = vs `mappend` replicate n Unit

lookupL :: (IntDomain i) =>  Int -> LocVars i -> AbstrValue i
lookupL i ls = lookupL' i ls
  where
    lookupL' _ []    = error $ "Jat.PState.Frame.lookupL: invalid index." ++ show i
    lookupL' 0 (f:_) = f
    lookupL' j (_:fs)= lookupL' (j-1) fs

updateL :: Int -> AbstrValue i -> LocVars i -> LocVars i
updateL i v vs = take i vs ++ v : drop (i+1) vs

--mapValuesL :: (AbstrValue i -> AbstrValue i) -> LocVars i -> LocVars i
--mapValuesL = fmap

elemsL :: LocVars i -> [AbstrValue i]
elemsL = id

--type OpStk i   = [(AbstrValue i, Path)]

--emptyS :: OpStk i
--emptyS = []

elemsS :: Stk i -> [AbstrValue i]
elemsS = id

--mapValuesS :: (AbstrValue i -> AbstrValue i) -> OpStk i -> OpStk i
--mapValuesS f = map (\(v,p) -> (f v,p))



--data Root = RStk Int Int | RLoc Int Int deriving (Eq,Show)
--data Path = Path (Root, [(P.ClassId, P.FieldId)]) | Empty deriving (Eq,Show)

--(-->) :: (P.ClassId, P.FieldId) -> Path -> Path
--k --> (Path (r, ks)) = Path (r, ks++[k])
--_ --> Empty          = error "Jat.State.Path: invalid composing of path"

instance (Pretty i) => Pretty (Frame i) where
  pretty (Frame loc stk cn mn pc) = text (show pc) `sepx` prettyLoc `sepx` prettyStk `sepx` pretty cn `sepx` pretty mn
    where
      sepx d f  = d <+> text "|" <+> f
      prettyLoc = encloseSep lbracket rbracket comma (map pretty $ elemsL loc)
      prettyStk = encloseSep lbracket rbracket comma (map pretty $ elemsS stk)
