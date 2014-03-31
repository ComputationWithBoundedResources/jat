{-# LANGUAGE TypeOperators #-}
module JFlow.Instances where

import JFlow.Data
import JFlow.Typing
import JFlow.PairSharing
--import JFlow.TreeShaped
{-import JFlow.Acyclic-}
import JFlow.ReachAC

import qualified Jat.PairSet as PS
import qualified Data.Set as S

import Jinja.Program

import JFlow.Data
import Text.PrettyPrint.ANSI.Leijen

data PFact = PFact TypingFact SharingFact RACFact deriving (Eq, Ord)

instance Pretty PFact where
  pretty (PFact ty sh ac) = hang 2 $ text "Fact:" <$> pretty ty <$> pretty sh <$> pretty ac

instance Show PFact where
  show p = flip displayS "" . renderPretty 0.2 300 $ pretty p

sharingVars :: PFact -> [(Var,Var)]
sharingVars (PFact _ sh _) = maySharingVars sh

reachingVars :: PFact -> [(Var,Var)]
reachingVars (PFact _ _ ac) = mayReachingVars ac

acyclicVars :: PFact -> [Var]
acyclicVars (PFact ty _ ac) = filter (not . isAcyclic ac) (vars ty)

instance HasIndexQ PFact where
  hasIndexQ (PFact ty _ _) = hasIndexQ ty
instance HasTypeQ PFact where
  hasTypeQ (PFact ty _ _) = hasTypeQ ty
instance MayShareQ PFact where
  mayShareQ (PFact _ sh _) x y = mayShareQ sh x y
instance MaySharesWithQ PFact where
  maySharesWithQ (PFact _ sh _) x = maySharesWithQ sh x
instance MayReachQ PFact where
  mayReachQ (PFact _ _ rac) x y = mayReachQ rac x y
instance MayReachesQ PFact where 
  mayReachesQ (PFact _ _ rac) x = mayReachesQ rac x
instance IsAcyclicQ PFact  where 
  isAcyclicQ (PFact _ _ rac) x = isAcyclicQ rac x

pFlow :: Flow PFact PFact
pFlow = Flow pLattice pTransfer

shFlow' :: Flow SharingFact PFact
shFlow' = shFlow

acFlow' :: Flow RACFact PFact
acFlow' = racFlow

pLattice :: SemiLattice PFact
pLattice = SemiLattice pname pbot pjoin
  where
    SemiLattice tyname tybot tyjoin = lattice tyFlow
    SemiLattice shname shbot shjoin = lattice shFlow'
    SemiLattice acname acbot acjoin = lattice acFlow'
    pname = "TYxSHxRxAC"
    pbot = PFact tybot shbot acbot
    pjoin p (PFact ty1 sh1 ac1) (PFact ty2 sh2 ac2) = PFact ty3 sh3 ac3
      where
        ty3 = tyjoin p ty1 ty2
        sh3 = shjoin p sh1 sh2
        ac3 = acjoin p ac1 ac2

pTransfer :: Transfer PFact PFact
pTransfer = Transfer pTransferf pSetup pProject pExtend
  where
    Transfer tyTransferf tySetup tyProject tyExtend = transfer tyFlow
    Transfer shTransferf shSetup shProject shExtend = transfer shFlow'
    Transfer acTransferf acSetup acProject acExtend = transfer acFlow'

    pTransferf p ins w v@(PFact ty sh ac) = PFact ty' sh' ac'
      where 
        ty' = tyTransferf p ins w ty 
        sh' = shTransferf p ins (PFact ty' sh ac) sh
        ac' = acTransferf p ins (PFact ty' sh ac) ac

    pSetup p cn mn = PFact (tySetup p cn mn) (shSetup p cn mn) (acSetup p cn mn)
    pProject p cn mn i w v@(PFact ty sh ac) = 
      PFact (proj tyProject ty) (proj shProject sh) (proj acProject ac)
      where proj f = f p cn mn i w
    pExtend p cn i w (PFact ty1 sh1 ac1) (PFact ty2 sh2 ac2) = 
      PFact (ext tyExtend ty1 ty2) (ext shExtend sh1 sh2) (ext acExtend ac1 ac2)
      where ext f v v' = f p cn i w v v'



--mkFlow2 :: (Show v, Show v') => P.Program -> Flow v -> Flow v' -> Flow (v :*: v')
{-type PairFlow = (TypingFact :>: (SharingFact :*: AcyclicFact))-}
{-pairFlow p = mkFlow2' p tyFlow (mkFlow2 p shFlow acFlow)-}
{-acyclicVars (_:>:(_:*:AcFact (Ac ac))) = S.elems ac-}

--type PairFlow = (TypingFact :>: (SharingFact :*: RACFact))

--pairFlow :: Program -> Flow PairFlow
--pairFlow p = mkFlow2' p tyFlow (mkFlow2 p shFlow racFlow)

--sharingVars :: PairFlow -> [(Var,Var)]
--sharingVars (_:>:(ShFact sh:*:_)) = PS.toList sh

--reachingVars :: PairFlow -> [(Var,Var)]
--reachingVars (_:>:(_:*:RACFact rs _)) = map (\(x:~>:y) -> (x,y)) $ S.toList rs

--acyclicVars :: PairFlow -> [Var]
--acyclicVars (ty:>:(_:*:RACFact _ cs)) = filter (flip S.notMember cs) (vars ty)
--acyclicVars _ = undefined




