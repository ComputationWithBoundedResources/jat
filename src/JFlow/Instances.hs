{-# LANGUAGE TypeOperators #-}
module JFlow.Instances where

import JFlow.Data
import JFlow.Typing2
import JFlow.PairSharing2
import JFlow.TreeShaped2
import JFlow.ReachAC

import qualified Jat.PairSet as PS
import qualified Data.Set as S

import Jinja.Program

type PairFlow = (TypingFact :>: (SharingFact :*: TreeShapedFact))

pairFlow :: Program -> Flow PairFlow
pairFlow p = mkFlow2' p tyFlow (mkFlow2 p shFlow tsFlow)

sharingVars :: PairFlow -> [(Var,Var)]
sharingVars (_:>:(ShFact sh:*:_)) = PS.toList sh

treeShapedVars :: PairFlow -> [Var]
treeShapedVars (_:>:(_:*:TsFact (Ts ts))) = S.elems ts
treeShapedVars _ = undefined


