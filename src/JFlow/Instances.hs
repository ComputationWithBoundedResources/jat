{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module JFlow.Instances where

import JFlow.Data
import JFlow.Typing
import JFlow.PairSharing
--import JFlow.TreeShaped
{-import JFlow.Acyclic-}
import JFlow.ReachAC
import JFlow.PointsTo

import qualified Jat.PairSet as PS
import qualified Data.Set as S

import Jinja.Program

import JFlow.Data
import Text.PrettyPrint.ANSI.Leijen


infixr 6 :>:
infixr 7 :*:

data a :>: b = a :>: b deriving (Eq, Ord)
data a :*: b = a :*: b deriving (Eq, Ord)

instance (Pretty a, Pretty b) => Pretty (a:>:b) where
  pretty (a:>:b) = hang 2 $ text "Fact:" <$> pretty a <$> pretty b

instance (Pretty a, Pretty b) => Pretty (a:*:b) where
  pretty (a:*:b) = pretty a <$> pretty b

mkFlow p (Flow lat1 tran1) (Flow lat2 tran2) = Flow lat3 tran3
  where
    lat3 = SemiLattice name3 bot3 join3
      where
        name3 = name lat1 ++ ":>:" ++ name lat2
        bot3  = bot lat1:>:bot lat2
        join3 _ (v1:>:v2) (v1':>:v2') = join lat1 p v1 v1':>:join lat2 p v2 v2'

    tran3 = Transfer transf3 setup3 project3 extend3
      where
        transf3 p ploc ins (w',w) (v1:>:v2) = v1':>:v2'
          where
            v1' = transf tran1 p ploc ins (w',w) v1
            v2' = transf tran2 p ploc ins (w',v1':>:v2) v2

        setup3 p cn mn = set tran1 :>: set tran2
          where set f = setup f p cn mn
        project3 p cn mn i w (v1 :>: v2) = proj tran1 v1 :>: proj tran2 v2
          where proj f = project f p cn mn i w
        extend3 p q cn i (old1 :>: old2) (new1 :>: new2) = ext tran1 old1 new1:>:ext tran2 old2 new2
          where ext f = extend f p q cn i

mkFlow' p (Flow lat1 tran1) (Flow lat2 tran2) = Flow lat3 tran3
  where
    lat3 = SemiLattice name3 bot3 join3
      where
        name3 = name lat1 ++ ":*:" ++ name lat2
        bot3  = bot lat1:*:bot lat2
        join3 _ (v1:*:v2) (v1':*:v2') = join lat1 p v1 v1':*:join lat2 p v2 v2'

    tran3 = Transfer transf3 setup3 project3 extend3
      where
        transf3 p ploc ins (w',w) (v1:*:v2) = v1':*:v2'
          where
            v1' = transf tran1 p ploc ins (w',w) v1
            v2' = transf tran2 p ploc ins (w',w) v2

        setup3 p cn mn = set tran1 :*: set tran2
          where set f = setup f p cn mn
        project3 p cn mn i w (v1 :*: v2) = proj tran1 v1 :*: proj tran2 v2
          where proj f = project f p cn mn i w
        extend3 p q cn i (old1 :*: old2) (new1 :*: new2) = ext tran1 old1 new1:*:ext tran2 old2 new2
          where ext f = extend f p q cn i


-- pfact
type PFact = TypingFact:>:SharingFact:*:RACFact

instance Show PFact where
  show p = flip displayS "" . renderPretty 0.2 300 $ pretty p

sharingVars :: PFact -> [(Var,Var)]
sharingVars (_:>:sh:*:_) = maySharingVars sh

reachingVars :: PFact -> [(Var,Var)]
reachingVars (_:>:_:*:ac) = mayReachingVars ac

acyclicVars :: PFact -> [Var]
acyclicVars (ty:>:_:*:ac) = filter (isAcyclic ac) (vars ty)

instance HasIndexQ PFact where
  hasIndexQ (ty:>:_:*:_) = hasIndexQ ty
instance HasTypeQ PFact where
  hasTypeQ (ty:>:_:*:_) = hasTypeQ ty
instance MayShareQ PFact where
  mayShareQ (_:>:sh:*:_) x y = mayShareQ sh x y
instance MaySharesWithQ PFact where
  maySharesWithQ (_:>:sh:*:_) x = maySharesWithQ sh x
instance MayReachQ PFact where
  mayReachQ (_:>:_:*:rac) x y = mayReachQ rac x y
instance MayReachesQ PFact where 
  mayReachesQ (_:>:_:*:rac) x = mayReachesQ rac x
instance IsAcyclicQ PFact  where 
  isAcyclicQ (_:>:_:*:rac) x = isAcyclicQ rac x
instance MayAliasQ PFact where
  mayAliasQ = mayShareQ

pFlow :: Program-> Flow(TypingFact :>: (SharingFact :*: RACFact))(TypingFact :>: (SharingFact :*: RACFact))
pFlow p = mkFlow p tyFlow $ mkFlow' p shFlow racFlow


-- pfact plus

type PFactP = TypingFact:>:PointsToFact:*:SharingFact:*:RACFact

instance Show PFactP where
  show p = flip displayS "" . renderPretty 0.2 300 $ pretty p

sharingVarsP :: PFactP -> [(Var,Var)]
sharingVarsP (_:>:_:*:sh:*:_) = maySharingVars sh

reachingVarsP :: PFactP -> [(Var,Var)]
reachingVarsP (_:>:_:*:_:*:ac) = mayReachingVars ac

acyclicVarsP :: PFactP -> [Var]
acyclicVarsP (ty:>:_:*:_:*:ac) = filter (isAcyclic ac) (vars ty)

instance HasIndexQ PFactP where
  hasIndexQ (ty:>:_:*:_:*:_) = hasIndexQ ty
instance HasTypeQ PFactP where
  hasTypeQ (ty:>:_:*:_:*:_) = hasTypeQ ty
instance MayShareQ PFactP where
  mayShareQ (_:>:_:*:sh:*:_) x y = mayShareQ sh x y
instance MaySharesWithQ PFactP where
  maySharesWithQ (_:>:_:*:sh:*:_) x = maySharesWithQ sh x
instance MayReachQ PFactP where
  mayReachQ (_:>:_:*:_:*:rac) x y = mayReachQ rac x y
instance MayReachesQ PFactP where 
  mayReachesQ (_:>:_:*:_:*:rac) x = mayReachesQ rac x
instance IsAcyclicQ PFactP  where 
  isAcyclicQ (_:>:_:*:_:*:rac) x = isAcyclicQ rac x
instance MayAliasQ PFactP where
  mayAliasQ (_:>:pt:*:_:*:_) x y = mayAliasQ pt x y

pFlowP :: Program-> Flow PFactP PFactP
pFlowP p = mkFlow p tyFlow $ mkFlow' p ptFlow $ mkFlow' p shFlow racFlow
