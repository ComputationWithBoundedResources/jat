{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module JFlow.ReachAC where


import Jinja.Program

import JFlow.Data hiding (isAcyclic)
import qualified JFlow.Data as D (isAcyclic)

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

isAcyclic :: Var -> Cyclic -> Bool
isAcyclic = S.notMember



data RACFact = RACFact Reaching Cyclic  deriving (Eq,Ord)

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

racFlow :: Flow RACFact
racFlow = Flow racLattice racTransfer racQueryV

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

racTransfer :: Transfer RACFact
racTransfer = Transfer racTransferf racSetup racProject racExtend
  where
    normalize' p q = normalize shTypes cyType
      where
        shTypes x y = areSharingTypes p (hasTypeQ q x) (hasTypeQ q y)
        cyType x    = isAcyclicType p (hasTypeQ q x)
      

    x `to` y = \z -> if z == x then y else z
    assign x y rac = rac' `union` rename (y `to` x) rac'
      where rac' = x `delete` rac

    racTransferf p q ins rac =
      let (i,j) = hasIndexQ q in racTransferf' p q ins rac i j
    racTransferf' p q ins rac@(RACFact rs cs) i j = case ins of
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
          rs' = S.fromList [ y :~>: x | y <- maySharesWithQ q x]

      PutField fn cn  -> delete val . delete ref $
        if isPrimitiveType $ snd (field p cn fn)
          then rac
          else reduce $ RACFact (rs `S.union` rs') (cs `S.union` cs')
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

    racSetup _ _ _ = RACFact S.empty S.empty

    racProject _ q _ _ nparams = rename to
      where
        (i,j)  = hasIndexQ q
        to z = z `fromMaybe` lookup z (zip [StkVar i k | k <- [j,j-1..]] [LocVar (i+1) k | k <- [nparams,nparams-1..0]])

    racExtend _ q _ nparams _ ac =
      filter k1 k2 $ (rl `assign` rs) ac
      where
        (i,j) = hasIndexQ q
        (rs,rl) = (StkVar (i+1) 0, StkVar i (j -nparams))
        k (StkVar i2 _) = i2 <= i
        k (LocVar i2 _) = i2 <= i
        k1 (x:~>:y)     = k x && k y
        k2 x            = k x && k x

racQueryV :: QueryV RACFact
racQueryV = defaultQueryV {D.isAcyclic = isAcyclic', mayReach = mayReach', mayReaches = mayReaches'}
  where
    isAcyclic' (RACFact _ cs) x  = Just $ isAcyclic x cs
    mayReach' (RACFact rs _) x y = Just $ y `elem` reaches x rs
    mayReaches' (RACFact rs _) x = Just $ reaches x rs





