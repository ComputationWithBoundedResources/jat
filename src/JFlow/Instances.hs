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

import qualified Jat.PairSet as PS
import qualified Data.Set as S

import Jinja.Program

import JFlow.Data
import Text.PrettyPrint.ANSI.Leijen

{-data PFact = PFact TypingFact SharingFact RACFact deriving (Eq, Ord)-}

{-instance Pretty PFact where-}
  {-pretty (PFact ty sh ac) = hang 2 $ text "Fact:" <$> pretty ty <$> pretty sh <$> pretty ac-}

{-instance Show PFact where-}
  {-show p = flip displayS "" . renderPretty 0.2 300 $ pretty p-}

{-sharingVars :: PFact -> [(Var,Var)]-}
{-sharingVars (PFact _ sh _) = maySharingVars sh-}

{-reachingVars :: PFact -> [(Var,Var)]-}
{-reachingVars (PFact _ _ ac) = mayReachingVars ac-}

{-acyclicVars :: PFact -> [Var]-}
{-acyclicVars (PFact ty _ ac) = filter (isAcyclic ac) (vars ty)-}

{-instance HasIndexQ PFact where-}
  {-hasIndexQ (PFact ty _ _) = hasIndexQ ty-}
{-instance HasTypeQ PFact where-}
  {-hasTypeQ (PFact ty _ _) = hasTypeQ ty-}
{-instance MayShareQ PFact where-}
  {-mayShareQ (PFact _ sh _) x y = mayShareQ sh x y-}
{-instance MaySharesWithQ PFact where-}
  {-maySharesWithQ (PFact _ sh _) x = maySharesWithQ sh x-}
{-instance MayReachQ PFact where-}
  {-mayReachQ (PFact _ _ rac) x y = mayReachQ rac x y-}
{-instance MayReachesQ PFact where -}
  {-mayReachesQ (PFact _ _ rac) x = mayReachesQ rac x-}
{-instance IsAcyclicQ PFact  where -}
  {-isAcyclicQ (PFact _ _ rac) x = isAcyclicQ rac x-}

{-pFlow :: Flow PFact PFact-}
{-pFlow = Flow pLattice pTransfer-}

{-shFlow' :: Flow SharingFact PFact-}
{-shFlow' = shFlow-}

{-acFlow' :: Flow RACFact PFact-}
{-acFlow' = racFlow-}

{-pLattice :: SemiLattice PFact-}
{-pLattice = SemiLattice pname pbot pjoin-}
  {-where-}
    {-SemiLattice tyname tybot tyjoin = lattice tyFlow-}
    {-SemiLattice shname shbot shjoin = lattice shFlow'-}
    {-SemiLattice acname acbot acjoin = lattice acFlow'-}
    {-pname = "TYxSHxRxAC"-}
    {-pbot = PFact tybot shbot acbot-}
    {-pjoin p (PFact ty1 sh1 ac1) (PFact ty2 sh2 ac2) = PFact ty3 sh3 ac3-}
      {-where-}
        {-ty3 = tyjoin p ty1 ty2-}
        {-sh3 = shjoin p sh1 sh2-}
        {-ac3 = acjoin p ac1 ac2-}

{-pTransfer :: Transfer PFact PFact-}
{-pTransfer = Transfer pTransferf pSetup pProject pExtend-}
  {-where-}
    {-Transfer tyTransferf tySetup tyProject tyExtend = transfer tyFlow-}
    {-Transfer shTransferf shSetup shProject shExtend = transfer shFlow'-}
    {-Transfer acTransferf acSetup acProject acExtend = transfer acFlow'-}

    {-pTransferf p ins (w',w) v@(PFact ty sh ac) = PFact ty' sh' ac'-}
      {-where -}
        {-ty' = tyTransferf p ins (w',w) ty -}
        {-sh' = shTransferf p ins (w',(PFact ty' sh ac)) sh-}
        {-ac' = acTransferf p ins (w',(PFact ty' sh ac)) ac-}

    {-pSetup p cn mn = PFact (tySetup p cn mn) (shSetup p cn mn) (acSetup p cn mn)-}
    {-pProject p cn mn i w v@(PFact ty sh ac) = -}
      {-PFact (proj tyProject ty) (proj shProject sh) (proj acProject ac)-}
      {-where proj f = f p cn mn i w-}
    {-pExtend p cn i w (PFact ty1 sh1 ac1) (PFact ty2 sh2 ac2) = -}
      {-PFact (ext tyExtend ty1 ty2) (ext shExtend sh1 sh2) (ext acExtend ac1 ac2)-}
      {-where ext f v v' = f p cn i w v v'-}



type PFact = TypingFact:>:SharingFact:*:RACFact

{-instance Pretty PFact where-}
  {-pretty f = hang 2 $ text "Fact:" <$> pretty f-}

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

pFlow :: Program-> Flow(TypingFact :>: (SharingFact :*: RACFact))(TypingFact :>: (SharingFact :*: RACFact))
pFlow p = mkFlow p tyFlow $ mkFlow' p shFlow racFlow

shFlow' :: Flow SharingFact PFact
shFlow' = shFlow

acFlow' :: Flow RACFact PFact
acFlow' = racFlow


infixl 6 :>:
infixl 7 :*:

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
        transf3 p ins (w',w) (v1:>:v2) = v1':>:v2'
          where
            v1' = transf tran1 p ins (w',w) v1
            v2' = transf tran2 p ins (w',v1':>:v2) v2

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
        transf3 p ins (w',w) (v1:*:v2) = v1':*:v2'
          where
            v1' = transf tran1 p ins (w',w) v1
            v2' = transf tran2 p ins (w',w) v2

        setup3 p cn mn = set tran1 :*: set tran2
          where set f = setup f p cn mn
        project3 p cn mn i w (v1 :*: v2) = proj tran1 v1 :*: proj tran2 v2
          where proj f = project f p cn mn i w
        extend3 p q cn i (old1 :*: old2) (new1 :*: new2) = ext tran1 old1 new1:*:ext tran2 old2 new2
          where ext f = extend f p q cn i


{-mkFlow2' p (Flow lat1 tran1 quer1) (Flow lat2 tran2 quer2) = Flow lat3 tran3 quer3-}
  {-where-}
    {-lat3  = SemiLattice name3 bot3 join3-}
    {-tran3 = Transfer transf3 setup3 project3 extend3-}
    {-quer3 = QueryV hasIndex3 hasStkIndex3 hasType3 mayShare3 maySharesWith3 isAcyclic3 mayReach3 mayReaches3 isCyclic3-}

    {-name3 = name lat1 ++ 'X': name lat2-}
    {-bot3  = bot lat1 :>: bot lat2-}
    {-join3 _ (v1 :>: v2) (v1' :>: v2') = join lat1 p v1 v1' :>: join lat2 p v2 v2'-}

    {-hasIndex3      (v :>: v')     = hasIndex      quer1 v     `mplus` hasIndex      quer2 v'-}
    {-hasStkIndex3   (v :>: v') n   = hasStkIndex   quer1 v n   `mplus` hasStkIndex   quer2 v' n-}
    {-hasType3       (v :>: v') x   = hasType       quer1 v x   `mplus` hasType       quer2 v' x-}
    {-mayShare3      (v :>: v') x y = mayShare      quer1 v x y `mplus` mayShare      quer2 v' x y-}
    {-maySharesWith3 (v :>: v') x   = maySharesWith quer1 v x   `mplus` maySharesWith quer2 v' x -}
    {-isAcyclic3  (v :>: v') x      = isAcyclic  quer1 v x   `mplus` isAcyclic  quer2 v' x-}
    {-mayReach3   (v :>: v') x y = mayReach   quer1 v x y `mplus` mayReach   quer2 v' x y-}
    {-mayReaches3 (v :>: v') x   = mayReaches quer1 v x   `mplus` mayReaches quer2 v' x-}
    {-isCyclic3   (v :>: v') x   = isCyclic   quer1 v x   `mplus` isCyclic   quer2 v' x-}

    {-setup3 _ cn mn = setup tran1 p cn mn :>: setup tran2 p cn mn-}

    {-runQueryV' v = runQueryV v quer3-}

    {-project3 _ q cn mn i (v1 :>: v2) = w1 :>: w2-}
      {-where-}
        {-w1 = project tran1 p q cn mn i v1-}
        {-w2 = project tran2 p q cn mn i v2-}
    
    {-extend3 _ q cn i (old1 :>: old2) (new1 :>: new2) = v1 :>: v2-}
      {-where-}
        {-v1 = extend tran1 p q cn i old1 new1-}
        {-v2 = extend tran2 p q cn i old2 new2-}

    {-transf3 _ _ ins (v1 :>: v2) = w1 :>: w2-}
      {-where-}
        {-w1 = transf tran1 p q1 ins v1-}
        {-w2 = transf tran2 p q2 ins v2-}
        {-q1 = runQueryV' (v1 :>: v2)-}
        {-q2 = runQueryV' (w1 :>: v2)-}


{-mkFlow2 :: (Show v, Show v') => P.Program -> Flow v -> Flow v' -> Flow (v :*: v')-}

{-type PairFlow = (TypingFact :>: (SharingFact :*: AcyclicFact))-}
{-pairFlow p = mkFlow2' p tyFlow (mkFlow2 p shFlow acFlow)-}
{-acyclicVars (_:>:(_:*:AcFact (Ac ac))) = S.elems ac-}

{-type PairFlow = (TypingFact :>: (SharingFact :*: RACFact))-}

{-pairFlow :: Program -> Flow PairFlow-}
{-pairFlow p = mkFlow2' p tyFlow (mkFlow2 p shFlow racFlow)-}

{-sharingVars :: PairFlow -> [(Var,Var)]-}
{-sharingVars (_:>:(ShFact sh:*:_)) = PS.toList sh-}

{-reachingVars :: PairFlow -> [(Var,Var)]-}
{-reachingVars (_:>:(_:*:RACFact rs _)) = map (\(x:~>:y) -> (x,y)) $ S.toList rs-}

{-acyclicVars :: PairFlow -> [Var]-}
{-acyclicVars (ty:>:(_:*:RACFact _ cs)) = filter (flip S.notMember cs) (vars ty)-}
{-acyclicVars _ = undefined-}




