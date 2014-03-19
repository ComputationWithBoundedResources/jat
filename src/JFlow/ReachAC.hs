{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module JFlow.ReachAC where


import Jinja.Program

import JFlow.Data

import Prelude hiding (filter)
import qualified Data.Set as S
import Data.Maybe (fromMaybe)
import Text.PrettyPrint.ANSI.Leijen


data Reaches = Var:~>:Var deriving (Eq,Ord)
type Reaching = S.Set Reaches

instance Pretty Reaches where
  pretty (x:~>:y) = pretty x <> text "~>" <> pretty y
instance Show Reaches where
  show = show . pretty

reaches :: Var -> Reaching -> [Var]
reaches x = S.fold k []
  where k (y:~>:z) = if y == x then (z:) else id

reachable :: Var -> Reaching -> [Var]
reachable x = S.fold k []
  where k (z:~>:y) = if y == x then (z:) else id

type Cyclic = S.Set Var

maybeCyclic :: Var -> Cyclic -> Bool
maybeCyclic = S.member

data AcyclicityFact = AcFact Reaching Cyclic  deriving (Eq,Ord)

instance Pretty AcyclicityFact where
  pretty (AcFact rs cs) = 
    string "AcFact"
    <$> list (map pretty (S.elems rs))
    <$> list (map pretty (S.elems cs))
instance Show AcyclicityFact where
  show = show . pretty

reduce :: AcyclicityFact -> AcyclicityFact
reduce (AcFact rs cs) = AcFact rs' cs
  where rs' = S.filter (\(v1:~>:v2) -> v1 /= v2 || maybeCyclic v1 cs) rs

rename :: (Var -> Var) -> AcyclicityFact -> AcyclicityFact
rename f (AcFact rs cs) = AcFact (k `S.map` rs) (f `S.map` cs)
  where k (x:~>:y) = f x:~>:f y

union :: AcyclicityFact -> AcyclicityFact -> AcyclicityFact
union (AcFact rs1 cs1) (AcFact rs2 cs2) = AcFact (rs1 `S.union` rs2) (cs1 `S.union` cs2)

delete :: Var -> AcyclicityFact -> AcyclicityFact
delete x (AcFact rs cs) = AcFact (x `rdelete` rs) (x `S.delete` cs)
  where rdelete x = S.filter (\(y:~>:z) -> x /= y && x /= z)

filter :: (Reaches -> Bool) -> (Var -> Bool) -> AcyclicityFact -> AcyclicityFact
filter f g (AcFact rs cs) = AcFact (S.filter f rs) (S.filter g cs)

acFlow :: Flow AcyclicityFact
acFlow = Flow acLattice acTransfer acQueryV

acLattice :: SemiLattice AcyclicityFact
acLattice = SemiLattice acName acBot acJoin
  where
    acName   = "Acyclicity"
    acBot    = AcFact S.empty S.empty
    acJoin _ = union

normalize :: (Var -> Var  -> Bool) -> (Var -> Bool) -> AcyclicityFact -> AcyclicityFact
normalize shTypes cyType (AcFact rs cs) = AcFact rs' cs'
  where
    rs' = S.filter (\(v1:~>:v2) -> shTypes v1 v2) rs
    cs' = S.filter cyType cs

acTransfer :: Transfer AcyclicityFact
{-acTransfer = Transfer shTransferf shSetup shProject shExtend-}
acTransfer = Transfer acTransferf acSetup acProject shExtend
  where
    {-normalize p q = normalize -}
      {-where ty (x:><:y) = areSharingTypes p (hasTypeQ q x) (hasTypeQ q y)-}

    x `to` y = \z -> if z == x then y else z
    assign x y ac = ac' `union` rename (y `to` x) ac'
      where ac' = x `delete` ac

    acTransferf p q ins ac =
      let (i,j) = hasIndexQ q in acTransferf' p q ins ac i j
    acTransferf' p q ins ac@(AcFact rs cs) i j = case ins of
      Load n          -> (StkVar i j `assign` LocVar i n) ac
      Store n         -> let (x,y) = (LocVar i n, StkVar i (j+1)) in  y `delete` ((x `assign` y) ac)
      Push _          -> ac
      Pop             -> StkVar i j `delete` ac
      IAdd            -> ac
      ISub            -> ac
      ICmpGeq         -> ac
      Goto _          -> ac
      IfFalse _       -> ac
      BNot            -> ac
      BOr             -> ac
      BAnd            -> ac
      CmpEq           -> StkVar i (j+1) `delete` (StkVar i j `delete` ac)
      CmpNeq          -> StkVar i (j+1) `delete` (StkVar i j `delete` ac)
      New _           -> ac
      {-CheckCast _     -> normalize p q sh-}
      GetField fn cn  ->
        if isPrimitiveType $ snd (field p cn fn)
          then x `delete` ac
          else reduce $ AcFact (rs `S.union` rs') cs
        where
          x = StkVar i j
          rs' = rs `S.union` S.fromList [ y :~>: x | y <- maySharesWithQ q x]

      PutField fn cn  -> delete val . delete ref $
        if isPrimitiveType $ snd (field p cn fn)
          then ac
          else reduce $ AcFact (rs `S.union` rs') (cs `S.union` cs')
          where
            (val,ref) = (StkVar i (j+2), StkVar i (j+1))
            aliasWith = maySharesWithQ q
            alias     = mayShareQ q
            rs' = S.fromList [ w1 :~>: w2 | w1 <- lhs1, w2 <- rhs1 ]
            lhs1 = aliasWith ref ++ ref `reachable` rs
            rhs1 = aliasWith val ++ val `reaches` rs
            cs' = S.fromList [ x | lhs2, x <- rhs2]
            lhs2 = maybeCyclic val cs || ref `elem` (val `reaches` rs) || val `alias` ref
            rhs2 = aliasWith val ++ val `reachable` rs
      Return          -> undefined
      Invoke _ _      -> undefined

    acSetup _ _ _ = AcFact S.empty S.empty

    acProject _ q _ _ nparams = rename to
      where
        (i,j)  = hasIndexQ q
        to z = z `fromMaybe` lookup z (zip [StkVar i k | k <- [j,j-1..]] [LocVar (i+1) k | k <- [nparams,nparams-1..0]])

    shExtend _ q _ nparams _ ac =
      filter k1 k2 $ (rl `assign` rs) ac
      where
        (i,j) = hasIndexQ q
        (rs,rl) = (StkVar (i+1) 0, StkVar i (j -nparams))
        k (StkVar i2 _) = i2 <= i
        k (LocVar i2 _) = i2 <= i
        k1 (x:~>:y)     = k x && k y
        k2 x            = k x && k x

acQueryV :: QueryV AcyclicityFact
acQueryV = defaultQueryV
--acQueryV = defaultQueryV{ isAcyclic = tsIsTreeShaped }
  --where tsIsTreeShaped (AcFact _ cs) x = Just . not $ maybeCyclic x cs



