{-# LANGUAGE TypeOperators #-}
module JFlow.Instances where

import JFlow.Data
import JFlow.Typing
import JFlow.PairSharing
import JFlow.TreeShaped
import JFlow.ReachAC

import qualified Jat.PairSet as PS
import qualified Data.Set as S

import Jinja.Program

type PairFlow = (TypingFact :>: (SharingFact :*: TreeShapedFact))
{-type PairFlow = (TypingFact :>: (SharingFact :*: AcyclicityFact))-}

pairFlow :: Program -> Flow PairFlow
pairFlow p = mkFlow2' p tyFlow (mkFlow2 p shFlow tsFlow)
{-pairFlow p = mkFlow2' p tyFlow (mkFlow2 p shFlow acFlow)-}

sharingVars :: PairFlow -> [(Var,Var)]
sharingVars (_:>:(ShFact sh:*:_)) = PS.toList sh

treeShapedVars :: PairFlow -> [Var]
treeShapedVars (_:>:(_:*:TsFact (Ts ts))) = S.elems ts
{-treeShapedVars (_:>:(_:*:(AcFact rs cs))) = S.elems cs-}
treeShapedVars _ = undefined


