module Jat.PState.MemoryModel.UnSharing where


import Jat.JatM
import Jat.PState.MemoryModel.Data
import Jat.Utils.Pretty

import qualified Data.Set as S

data MayShare = Int :><: Int deriving Show
data MayAlias = Int :=?: Int deriving Show
data MayGraph = NT Int deriving (Eq,Ord,Show)

instance Eq MayShare where
  q1:><:q2 == r1:><:r2 = 
    (q1 == r1 && q2 == r2) ||
    (q1 == r2 && q2 == r1) 

instance Ord MayShare where
  qs `compare` rs = compare (ord qs) (ord rs)
    where ord (q1:><:q2) = if q1 > q2 then (q1,q2) else (q2,q1)

instance Pretty MayShare where
  pretty (q1:><:q2) = text $ show q1 ++ "><" ++ show q2

instance Eq MayAlias where
  q1:=?:q2 == r1:=?:r2 = 
    (q1 == r1 && q2 == r2) ||
    (q1 == r2 && q2 == r1) 

instance Ord MayAlias where
  qs `compare` rs = compare (ord qs) (ord rs)
    where ord (q1:=?:q2) = if q1 > q2 then (q1,q2) else (q2,q1)

instance Pretty MayAlias where
  pretty (q1:=?:q2) = text $ show q1 ++ "=?" ++ show q2

instance Pretty MayGraph where
  pretty (NT q) = text $ "&" ++ show q

data UnSharing = UnSharing (S.Set MayShare) (S.Set MayAlias) (S.Set MayGraph) deriving (Eq,Ord,Show)

instance Pretty UnSharing where
  pretty (UnSharing ms ma mg) =
    vsep $ map pretty (S.elems ms)
    <$> vsep $ map pretty (S.elems ma)
    <$> vsep $ map pretty (S.elems mg)

instance MemoryModel UnSharing where
  new       = undefined  
  getField  = undefined
  putField  = undefined

  invoke    = undefined
  equals    = undefined
  nequals   = undefined

  initMem   = undefined

  leq       = undefined
  join      = undefined

  state2TRS = undefined









