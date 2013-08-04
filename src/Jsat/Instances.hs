{-# LANGUAGE TypeOperators #-}
module Jsat.Instances where

import Jsat.Data
import Jsat.Typing2
import Jsat.PairSharing2
import Jsat.TreeShaped2

import qualified Jat.PairSet as PS
import qualified Data.Set as S

import Jat.Program

type PairFlow = (TypingFact :>: (SharingFact :*: TreeShapedFact))

pairFlow :: Program -> Flow PairFlow
pairFlow p = mkFlow2' p tyFlow (mkFlow2 p shFlow tsFlow)

sharingVars :: PairFlow -> [(Var,Var)]
sharingVars (_:>:(ShFact sh:*:_)) = PS.toList sh

treeShapedVars :: PairFlow -> [Var]
treeShapedVars (_:>:(_:*:TsFact (Ts ts))) = S.elems ts
treeShapedVars _ = undefined


