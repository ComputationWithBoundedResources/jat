-- | Treeshaped domain following (adapting) 'Detecting Non-cyclicity by
-- Abstract Compilation into Boolean Functions' by S. rossignoli and F. Spoto

-- Here, type constriction considers treeshaped rather than non-cyclicity 
-- ie. class A { C a; C b} with Class C { f = int } can be non-tree shaped but not cyclic
-- Otherwise, the presented field update interpretation captures (safely) treeshaped forms

module JFlow.TreeShaped where

import Jinja.Program as P 

import JFlow.Data

import Data.Maybe (fromMaybe)
import Text.PrettyPrint.ANSI.Leijen
import qualified Data.Set as S

{-import Debug.Trace-}

newtype TreeShapedFact = TsFact TS  deriving (Eq,Ord)
data TS = TsTop | Ts (S.Set Var) deriving (Eq,Ord)

instance Pretty TreeShapedFact where
  pretty (TsFact TsTop)   = string "TsFact" <$> string "TsTop"
  pretty (TsFact (Ts ts)) = 
    string "TsFact" 
    <$> list (map ((char '^' <>). pretty) $ S.elems ts)

instance Show TreeShapedFact where
  show = show . pretty 

tsFlow :: Flow TreeShapedFact
tsFlow = Flow tsLattice tsTransfer tsQueryV

tsLattice :: SemiLattice TreeShapedFact
tsLattice = SemiLattice tsName tsBot tsJoin
  where
    tsName = "TreeShaped"
    tsBot  = TsFact TsTop

    tsJoin _ (TsFact TsTop) (TsFact ts)          = TsFact ts
    tsJoin _ (TsFact ts) (TsFact TsTop)          = TsFact ts
    tsJoin _ (TsFact (Ts ts1)) (TsFact (Ts ts2)) = TsFact (Ts ts3)
      where ts3 = ts1 `S.intersection` ts2

tsTransfer :: Transfer TreeShapedFact
tsTransfer = Transfer tsTransferf tsSetup tsProject tsExtend
  where
    assign x y ts
      | y `S.member` ts = x `S.insert` ts
      | otherwise       = x `S.delete` ts
      
    tsTransferf _ _ _   (TsFact  TsTop)  = undefined
    tsTransferf p q ins (TsFact (Ts ts)) = 
      let (i,j) = hasIndexQ q in tsTransferf' p q ins ts i j
    tsTransferf' p q ins ts i j = TsFact . Ts $ case ins of
      Load n       -> (StkVar i j `assign` LocVar i n) ts
      Store n      -> let (x,y) = (LocVar i n, StkVar i (j+1)) in S.delete y $ (x `assign` y) ts
      Push _       -> StkVar i j `S.insert` ts
      New _        -> StkVar i j `S.insert` ts
      CheckCast _  -> ts
      Pop          -> StkVar i (j+1) `S.delete` ts
      IAdd         -> StkVar i (j+1) `S.delete` ts
      ISub         -> StkVar i (j+1) `S.delete` ts
      Goto _       -> ts
      IfFalse _    -> StkVar i (j+1) `S.delete` ts
      CmpEq        -> S.insert (StkVar i j) $ S.delete (StkVar i (j+1)) ts
      CmpNeq       -> S.insert (StkVar i j) $ S.delete (StkVar i (j+1)) ts
      ICmpGeq      -> StkVar i (j+1) `S.delete` ts
      BNot         -> ts
      BOr          -> StkVar i (j+1) `S.delete` ts
      BAnd         -> StkVar i (j+1) `S.delete` ts
      Return       -> undefined
      Invoke _ _   -> undefined

      GetField fn cn  -> if isTreeShaped' p cn fn then StkVar i j `S.insert` ts else ts
      PutField fn cn  -> S.delete val . S.delete ref $
                        if isTreeShaped' p cn fn || (val `S.member` ts && not (shares val ref))
                          then ts
                          else ts `S.difference` sharesWith ref (S.elems ts) q
                        where 
                          (val,ref) = (StkVar i (j+2), StkVar i (j+1))
                          shares    = mayShareQ q
      
    isTreeShaped' p cn fn = P.isTreeShapedType p ty
      where ty = snd $ field p cn fn

    sharesWith x es q = S.fromList $ foldl k [] es
      where  k xs y = if  mayShareQ q x y then y:xs else xs


    tsSetup p cn mn = TsFact (Ts $ S.fromList [LocVar 0 i | i <- [0..nparams]])
      where
        md      = theMethod p cn mn
        nparams = length (methodParams md)

    tsProject _ q _ _ nparams (TsFact (Ts ts)) = TsFact (Ts $ S.map rename ts)
      where 
        (i,j)  = hasIndexQ q
        rename z = z `fromMaybe` lookup z (zip [StkVar i k | k <- [j,j-1..]] [LocVar (i+1) k | k <- [nparams,nparams-1..0]])
    tsProject _ _ _ _ _ tsf = tsf

    tsExtend _ q _ nparams _ (TsFact (Ts ts)) = 
      TsFact . Ts . S.filter k $ (rl `assign` rs) ts
      where 
        (i,j) = hasIndexQ q
        (rs,rl) = (StkVar (i+1) 0, StkVar i (j -nparams))
        k (StkVar i2 _) = i2 <= i
        k (LocVar i2 _) = i2 <= i
    tsExtend _ _ _ _ _ tsf = tsf
    

tsQueryV :: QueryV TreeShapedFact
tsQueryV = defaultQueryV{ isTreeShaped = tsIsTreeShaped }
  where
    tsIsTreeShaped (TsFact TsTop) _   = Just True
    tsIsTreeShaped (TsFact (Ts ts)) x = Just $ x `S.member` ts


