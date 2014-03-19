{-# LANGUAGE TypeOperators #-}
module JFlow.Instances where

import JFlow.Data
import JFlow.Typing
import JFlow.PairSharing
import JFlow.TreeShaped
import JFlow.Acyclic
--import JFlow.ReachAC

import qualified Jat.PairSet as PS
import qualified Data.Set as S

import Jinja.Program

type PairFlow = (TypingFact :>: (SharingFact :*: AcyclicFact))
{-type PairFlow = (TypingFact :>: (SharingFact :*: AcyclicityFact))-}

pairFlow :: Program -> Flow PairFlow
pairFlow p = mkFlow2' p tyFlow (mkFlow2 p shFlow acFlow)
{-pairFlow p = mkFlow2' p tyFlow (mkFlow2 p shFlow acFlow)-}

sharingVars :: PairFlow -> [(Var,Var)]
sharingVars (_:>:(ShFact sh:*:_)) = PS.toList sh

acyclicVars :: PairFlow -> [Var]
acyclicVars (_:>:(_:*:AcFact (Ac ac))) = S.elems ac
{-treeShapedVars (_:>:(_:*:(AcFact rs cs))) = S.elems cs-}
acyclicVars _ = undefined


