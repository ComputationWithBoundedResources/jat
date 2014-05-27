-- | Treeshaped domain following (adapting) 'Detecting Non-cyclicity by
-- Abstract Compilation into Boolean Functions' by S. rossignoli and F. Spoto

module JFlow.Acyclic where

import Jinja.Program as P 

import JFlow.Data

import Data.Maybe (fromMaybe)
import Text.PrettyPrint.ANSI.Leijen
import qualified Data.Set as S

--import Debug.Trace

newtype AcyclicFact = AcFact AC  deriving (Eq,Ord)
data AC = AcTop | Ac (S.Set Var) deriving (Eq,Ord)

instance Pretty AcyclicFact where
  pretty (AcFact AcTop)   = string "AcFact" <$> string "AcTop"
  pretty (AcFact (Ac ac)) = 
    string "AcFact" 
    <$> list (map ((char '^' <>). pretty) $ S.elems ac)

instance Show AcyclicFact where
  show = show . pretty 

acFlow :: Flow AcyclicFact
acFlow = Flow acLattice acTransfer acQueryV

acLattice :: SemiLattice AcyclicFact
acLattice = SemiLattice acName acBot acJoin
  where
    acName = "Acyclic"
    acBot  = AcFact AcTop

    acJoin _ (AcFact AcTop) (AcFact ac)          = AcFact ac
    acJoin _ (AcFact ac) (AcFact AcTop)          = AcFact ac
    acJoin _ (AcFact (Ac ac1)) (AcFact (Ac ac2)) = AcFact (Ac ac3)
      where ac3 = ac1 `S.intersection` ac2

acTransfer :: Transfer AcyclicFact
acTransfer = Transfer acTransferf acSetup acProject acExtend
  where
    assign x y ac
      | y `S.member` ac = x `S.insert` ac
      | otherwise       = x `S.delete` ac
      
    acTransferf _ _ _   (AcFact  AcTop)  = undefined
    acTransferf p q ins (AcFact (Ac ac)) = 
      let (i,j) = hasIndexQ q in acTransferf' p q ins ac i j
    acTransferf' p q ins ac i j = AcFact . Ac $ case ins of
      Load n       -> (StkVar i j `assign` LocVar i n) ac
      Store n      -> let (x,y) = (LocVar i n, StkVar i (j+1)) in S.delete y $ (x `assign` y) ac
      Push _       -> StkVar i j `S.insert` ac
      New _        -> StkVar i j `S.insert` ac
      CheckCast _  -> ac
      Pop          -> StkVar i (j+1) `S.delete` ac
      IAdd         -> StkVar i (j+1) `S.delete` ac
      ISub         -> StkVar i (j+1) `S.delete` ac
      Goto _       -> ac
      IfFalse _    -> StkVar i (j+1) `S.delete` ac
      CmpEq        -> S.insert (StkVar i j) $ S.delete (StkVar i (j+1)) ac
      CmpNeq       -> S.insert (StkVar i j) $ S.delete (StkVar i (j+1)) ac
      ICmpGeq      -> StkVar i (j+1) `S.delete` ac
      BNot         -> ac
      BOr          -> StkVar i (j+1) `S.delete` ac
      BAnd         -> StkVar i (j+1) `S.delete` ac
      Return       -> undefined
      Invoke _ _   -> undefined

      GetField fn cn  -> if isAcyclic' p cn fn then StkVar i j `S.insert` ac else ac
      -- x.f = y; either y is already cyclic or there is a cycle with x
      -- TODO: check if normalising is necessary
      PutField fn cn -> S.delete val . S.delete ref $
        if isAcyclic' p cn fn 
          {-|| (val `S.member` ac && not (shares val ref))-}
          {-|| (val `S.member` ac && (maybe False ((cn `S.notMember`) . reachableClasses p) valty))-}
        then ac
        else ac `S.difference` sharesWith ref (S.elems ac) q
        where 
          (val,ref) = (StkVar i (j+2), StkVar i (j+1))
          shares    = mayShareQ q
          valty = case snd $ field p cn fn of
            RefType cn' -> Just cn'
            _           -> Nothing
      
    isAcyclic' p cn fn = P.isAcyclicType' p ty
      where ty = snd $ field p cn fn

    sharesWith x es q = S.fromList $ foldl k [] es
      where  k xs y = if  mayShareQ q x y then y:xs else xs


    acSetup p cn mn = AcFact (Ac $ S.fromList [LocVar 0 i | i <- [0..mx]])
      where
        md = theMethod p cn mn
        mx = maxLoc md + length (methodParams md)

    acProject _ q _ _ nparams (AcFact (Ac ac)) = AcFact (Ac $ S.map rename ac)
      where 
        (i,j)  = hasIndexQ q
        rename z = z `fromMaybe` lookup z (zip [StkVar i k | k <- [j,j-1..]] [LocVar (i+1) k | k <- [nparams,nparams-1..0]])
    acProject _ _ _ _ _ acf = acf

    acExtend _ q _ nparams _ (AcFact (Ac ac)) = 
      AcFact . Ac . S.filter k $ (rl `assign` rs) ac
      where 
        (i,j) = hasIndexQ q
        (rs,rl) = (StkVar (i+1) 0, StkVar i (j -nparams))
        k (StkVar i2 _) = i2 <= i
        k (LocVar i2 _) = i2 <= i
    acExtend _ _ _ _ _ acf = acf
    

acQueryV :: QueryV AcyclicFact
acQueryV = defaultQueryV{ isAcyclic = acIsAcyclic }
  where
    acIsAcyclic (AcFact AcTop) _   = Just True
    acIsAcyclic (AcFact (Ac ac)) x = Just $ x `S.member` ac


