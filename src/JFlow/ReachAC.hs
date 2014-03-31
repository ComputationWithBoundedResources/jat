{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module JFlow.ReachAC 
  (
    RACFact
  , racFlow
  , mayReach
  , mayReaches
  , mayReachingVars
  , isAcyclic
  )
where


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

isAcyclic' :: Var -> Cyclic -> Bool
isAcyclic' = S.notMember

data RACFact = RACFact Reaching Cyclic  deriving (Eq,Ord)

mayReach :: RACFact -> Var -> Var -> Bool  
mayReach (RACFact rs _) x y = y `elem` reaches x rs

mayReaches :: RACFact -> Var -> [Var]
mayReaches (RACFact rs _) x = reaches x rs

mayReachingVars :: RACFact -> [(Var,Var)]
mayReachingVars (RACFact rs _) = map (\(x:~>:y) -> (x,y)) $ S.toList rs

isAcyclic :: RACFact -> Var -> Bool
isAcyclic (RACFact _ cs) x = x `S.notMember` cs

instance MayReachQ RACFact        where mayReachQ = mayReach
instance MayReachesQ RACFact      where mayReachesQ = mayReaches
instance MayReachingVarsQ RACFact where mayReachingVarsQ = mayReachingVars
instance IsAcyclicQ RACFact       where isAcyclicQ = isAcyclic


instance Pretty RACFact where
  pretty (RACFact rs cs) = 
    string "RACFact"
    <$> list (map pretty (S.elems rs))
    <$> list (map pretty (S.elems cs))
instance Show RACFact where
  show = show . pretty

reduce :: RACFact -> RACFact
reduce (RACFact rs cs) = RACFact rs' cs
  where rs' = S.filter (\(v1:~>:v2) -> v1 /= v2 || maybeCyclic v1 cs) rs

rename :: (Var -> Var) -> RACFact -> RACFact
rename f (RACFact rs cs) = RACFact (k `S.map` rs) (f `S.map` cs)
  where k (x:~>:y) = f x:~>:f y

union :: RACFact -> RACFact -> RACFact
union (RACFact rs1 cs1) (RACFact rs2 cs2) = RACFact (rs1 `S.union` rs2) (cs1 `S.union` cs2)

delete :: Var -> RACFact -> RACFact
delete x (RACFact rs cs) = RACFact (x `rdelete` rs) (x `S.delete` cs)
  where rdelete x = S.filter (\(y:~>:z) -> x /= y && x /= z)

filter :: (Reaches -> Bool) -> (Var -> Bool) -> RACFact -> RACFact
filter f g (RACFact rs cs) = RACFact (S.filter f rs) (S.filter g cs)

racFlow :: (HasIndexQ w, HasTypeQ w, MayShareQ w, MaySharesWithQ w) => Flow RACFact w
racFlow = Flow racLattice racTransfer

racLattice :: SemiLattice RACFact
racLattice = SemiLattice racName racBot racJoin
  where
    racName   = "Reachability+Acyclicity"
    racBot    = RACFact S.empty S.empty
    racJoin _ = union

normalize :: (Var -> Var  -> Bool) -> (Var -> Bool) -> RACFact -> RACFact
normalize shTypes cyType (RACFact rs cs) = reduce $ RACFact rs' cs'
  where
    rs' = S.filter (\(v1:~>:v2) -> shTypes v1 v2) rs
    cs' = S.filter cyType cs

racTransfer :: (HasIndexQ w, HasTypeQ w, MayShareQ w, MaySharesWithQ w) => Transfer RACFact w
racTransfer = Transfer racTransferf racSetup racProject racExtend
  where
    normalize' p w = normalize shTypes cyType
      where
        shTypes x y = areSharingTypes p (hasTypeQ w x) (hasTypeQ w y)
        cyType x    = isAcyclicType p (hasTypeQ w x)
      

    x `to` y = \z -> if z == x then y else z
    assign x y rac = rac' `union` rename (y `to` x) rac'
      where rac' = x `delete` rac

    racTransferf p ins w rac =
      let (i,j) = hasIndexQ w in racTransferf' p ins w rac i j
    racTransferf' p ins w rac@(RACFact rs cs) i j = case ins of
      Load n          -> (StkVar i j `assign` LocVar i n) rac
      Store n         -> let (x,y) = (LocVar i n, StkVar i (j+1)) in  y `delete` ((x `assign` y) rac)
      Push _          -> rac
      Pop             -> StkVar i j `delete` rac
      IAdd            -> rac
      ISub            -> rac
      ICmpGeq         -> rac
      Goto _          -> rac
      IfFalse _       -> rac
      BNot            -> rac
      BOr             -> rac
      BAnd            -> rac
      CmpEq           -> StkVar i (j+1) `delete` (StkVar i j `delete` rac)
      CmpNeq          -> StkVar i (j+1) `delete` (StkVar i j `delete` rac)
      New _           -> rac

      {-CheckCast _     -> normalize p q rac-}
      GetField fn cn  ->
        if isPrimitiveType $ snd (field p cn fn)
          then x `delete` rac
          else reduce $ RACFact  (rs `S.union` rs') cs
        where
          x = StkVar i j
          rs' = S.fromList [ y :~>: x | y <- maySharesWithQ w x]

      PutField fn cn  -> delete val . delete ref $
        if isPrimitiveType $ snd (field p cn fn)
          then rac
          else reduce $ RACFact (rs `S.union` rs') (cs `S.union` cs')
          where
            (val,ref) = (StkVar i (j+2), StkVar i (j+1))
            aliasWith = maySharesWithQ w
            alias     = mayShareQ w
            rs' = S.fromList [ w1 :~>: w2 | w1 <- lhs1, w2 <- rhs1 ]
            lhs1 = aliasWith ref ++ ref `reachable` rs
            rhs1 = aliasWith val ++ val `reaches` rs
            cs' = S.fromList [ x | lhs2, x <- rhs2]
            lhs2 = maybeCyclic val cs || ref `elem` (val `reaches` rs) || val `alias` ref
            rhs2 = aliasWith val ++ val `reachable` rs
      Return          -> undefined
      Invoke _ _      -> undefined

    racSetup _ _ _ = RACFact S.empty S.empty

    racProject _ _ _ nparams w = rename to
      where
        (i,j)  = hasIndexQ w
        to z = z `fromMaybe` lookup z (zip [StkVar i k | k <- [j,j-1..]] [LocVar (i+1) k | k <- [nparams,nparams-1..0]])

    racExtend _ _ nparams w _ ac =
      filter k1 k2 $ (rl `assign` rs) ac
      where
        (i,j) = hasIndexQ w
        (rs,rl) = (StkVar (i+1) 0, StkVar i (j -nparams))
        k (StkVar i2 _) = i2 <= i
        k (LocVar i2 _) = i2 <= i
        k1 (x:~>:y)     = k x && k y
        k2 x            = k x && k x


