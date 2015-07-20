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
import Jat.Utils.Pretty

import JFlow.Data

import Prelude
import qualified Data.Set as S
import Data.Maybe (fromMaybe)

--import Debug.Trace

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

--isAcyclic' :: Var -> Cyclic -> Bool
--isAcyclic' = S.notMember

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
    <$> list (map (\v -> char '&' <> pretty v) (S.elems cs))
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
  where rdelete x1 = S.filter (\(y:~>:z) -> x1 /= y && x1 /= z)

filter' :: (Reaches -> Bool) -> (Var -> Bool) -> RACFact -> RACFact
filter' f g (RACFact rs cs) = RACFact (S.filter f rs) (S.filter g cs)

normalize :: (Var -> Var  -> Bool) -> (Var -> Bool) -> RACFact -> RACFact
normalize shTypes cyType ac = reduce $ filter' (\(v1:~>:v2) -> shTypes v1 v2) cyType ac

racFlow :: (HasIndexQ w, HasTypeQ w, MayShareQ w, MaySharesWithQ w, MayAliasQ w, Show w) => Flow RACFact w
racFlow = Flow racLattice racTransfer

racLattice :: SemiLattice RACFact
racLattice = SemiLattice racName racBot racJoin
  where
    racName   = "Reachability+Acyclicity"
    racBot    = RACFact S.empty S.empty
    racJoin _ = union


racTransfer :: (HasIndexQ w, HasTypeQ w, MayShareQ w, MaySharesWithQ w, MayAliasQ w, Show w) => Transfer RACFact w
racTransfer = Transfer racTransferf racSetup racProject racExtend
  where
    normalize' p w = normalize shTypes cyType
      where
        shTypes x y = areReachingTypes p (hasTypeQ w x) (hasTypeQ w y)
        cyType x    = not $ isAcyclicType p (hasTypeQ w x)

    {-singleField p dn cn fn = and $ single (subClassesOf p dn)-}
      {-where single cns = [ False | (fn',cn',ty') <- concatMap (hasFields p) cns, (fn' /= fn || cn' /= cn) && not (isAcyclicType' p ty')]-}

    {-singleField p-}
      

    x `to` y = \z -> if z == x then y else z
    assign x y rac = rac' `union` rename (y `to` x) rac'
      where rac' = x `delete` rac

    racTransferf p _ ins (w',w) rac =
      let (i,j) = hasIndexQ w in racTransferf' p ins (w',w) rac i j
    racTransferf' p ins (w',w) rac@(RACFact rs cs) i j = case ins of
      Load n          -> (StkVar i j `assign` LocVar i n) rac
      Store n         -> let (x,y) = (LocVar i n, StkVar i (j+1)) in  y `delete` (x `assign` y) rac
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

      CheckCast _     -> error "JFlow.ReachAC.CheckCast: not implemented" -- normalize p q rac
      GetField fn cn  ->
        if isPrimitiveType $ snd (field p cn fn)
          then x `delete` rac
          else normalize' p w $ RACFact  (rs `S.union` rs') cs
        where
          x = StkVar i j
          rs' = S.fromList [ y :~>: x | y <- maySharesWithQ w x]

      PutField _  _  | hasTypeQ w' (StkVar i (j+1)) == NullType -> RACFact S.empty S.empty
      PutField fn cn  -> delete val . delete ref $ RACFact rs1 cs1 `union` RACFact rs' cs'
        where
          (val,ref)   = (StkVar i (j+2), StkVar i (j+1))
          RefType tref = hasTypeQ w' ref

          cs1 = if singleCyclicField p tref (cn,fn) then ref `S.delete` cs else cs
          {-cs1 = cs-}
          rs1 = rs

          rs' = S.fromList [ w1 :~>: w2 | w1 <- lhs1, w2 <- rhs1 ]
            where
              lhs1 = aliasWith ref ++ ref `reachable` rs
              rhs1 = aliasWith val ++ val `reaches` rs

          cs' 
            | isAcyclic'' p cn fn = cs1
            | (val `S.notMember`) cs1 && not (val `mayShare` ref) = cs1
            | otherwise = S.fromList [ x | lhs, x <- rhs ]
            where
              lhs = ref `elem` (val `reaches` rs1) || val `alias` ref || maybeCyclic val cs1
              rhs = aliasWith val ++ val `reachable` rs

          isAcyclic'' p1 cn1 fn1 = isAcyclicType p (snd $ field p1 cn1 fn1)
          --hasType  = hasTypeQ w
          mayAlias = mayAliasQ w
          mayShare = mayShareQ w
          alias x y   = x `talias` y && x `mayShare` y  && x `mayAlias` y
          talias x y  = areRelatedTypes p (hasTypeQ w' x) (hasTypeQ w' y)
          aliasWith x = filter (\y -> x `talias` y && x `mayAlias` y) $ maySharesWithQ w x



      Return          -> undefined
      Invoke _ _      -> undefined

    racSetup _ _ _ = RACFact S.empty S.empty

    racProject _ _ _ nparams w = rename toV
      where
        (i,j) = hasIndexQ w
        toV z = z `fromMaybe` lookup z (zip [StkVar i k | k <- [j,j-1..]] [LocVar (i+1) k | k <- [nparams,nparams-1..0]])

    racExtend _ _ nparams w _ ac =
      filter' k1 k2 $ (rl `assign` rs) ac
      where
        (i,j) = hasIndexQ w
        (rs,rl) = (StkVar (i+1) 0, StkVar i (j -nparams))
        k (StkVar i2 _) = i2 <= i
        k (LocVar i2 _) = i2 <= i
        k1 (x:~>:y)     = k x && k y
        k2 x            = k x && k x

