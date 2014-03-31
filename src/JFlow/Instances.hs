{-# LANGUAGE TypeOperators #-}
module JFlow.Instances where

import JFlow.Data
import JFlow.Typing
import JFlow.PairSharing
import JFlow.TreeShaped
{-import JFlow.Acyclic-}
import JFlow.ReachAC hiding (filter)

import qualified Jat.PairSet as PS
import qualified Data.Set as S

import Jinja.Program

{-type PairFlow = (TypingFact :>: (SharingFact :*: AcyclicFact))-}
{-pairFlow p = mkFlow2' p tyFlow (mkFlow2 p shFlow acFlow)-}
{-acyclicVars (_:>:(_:*:AcFact (Ac ac))) = S.elems ac-}

type PairFlow = (TypingFact :>: (SharingFact :*: RACFact))

pairFlow :: Program -> Flow PairFlow
pairFlow p = mkFlow2' p tyFlow (mkFlow2 p shFlow racFlow)

sharingVars :: PairFlow -> [(Var,Var)]
sharingVars (_:>:(ShFact sh:*:_)) = PS.toList sh

acyclicVars :: PairFlow -> [Var]
acyclicVars (ty:>:(_:*:RACFact rs cs)) = filter (flip S.notMember cs) (vars ty)
acyclicVars _ = undefined




