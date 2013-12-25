-- | Treeshaped domain following (adapting) 'Detecting Non-cyclicity by
-- Abstract Compilation into Boolean Functions' by S. rossignoli and F. Spoto

-- Here, type constriction considers treeshaped rather than non-cyclicity 
-- ie. class A { C a; C b} with Class C { f = int } can be non-tree shaped but not cyclical
-- Otherwise, the presented field update interpretation captures (safely) treeshaped forms

module Jsat.TreeShaped where

import Jsat.Data
import Jsat.Program as P 

import Data.Maybe (fromJust)
import Text.PrettyPrint.ANSI.Leijen ((<+>),(<>))
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import qualified Data.Set as S


newtype TreeShapedFact = TsFact (Ts, [Var])  deriving (Eq,Ord)
data Ts = TsTop | Ts (S.Set Var) deriving (Eq,Ord)

instance Show TreeShapedFact where
  show (TsFact (ts,stk)) = show $
    PP.string "TsFact" <+> PP.lparen 
    <> PP.string (show ts) <+> PP.char '|' 
    <+> PP.string (show stk) <+> PP.string "||" <+> PP.int (length stk) <> PP.rparen

instance Show Ts where
  show TsTop   = "Top"
  show (Ts vs) = show $ S.elems vs

index :: [Var] -> Var
index []          = StkVar 0
index(StkVar i:_) = StkVar (i+1)
index _           = error "PairSharing.index: invalid stack"

tos :: [Var] -> Var
tos (StkVar i:_) = StkVar i
tos _            = error "PairSharing.tos: invalid stack"


tsFlow :: Flow TreeShapedFact
tsFlow = Flow tsLattice tsTransfer tsQueryV

tsLattice :: SemiLattice TreeShapedFact
tsLattice = SemiLattice tsName tsBot tsJoin
  where
    tsName = "TreeShaped"
    tsBot  = TsFact (TsTop,[])
    {-tsJoin _ (TsFact(_,stk1)) (TsFact(_,stk2)) -}
      {-| stk1 /= stk2 = error $ "tsJoin" -}
    tsJoin _ (TsFact(TsTop,stk1)) (TsFact(ts2,_))       = TsFact(ts2,stk1)
    tsJoin _ (TsFact(ts1,stk1)) (TsFact(TsTop,_))       = TsFact(ts1,stk1)
    tsJoin _ (TsFact(Ts ts1,stk1)) (TsFact(Ts ts2,_)) = TsFact(Ts ts3,stk1)
      where ts3 = ts1 `S.intersection` ts2

tsTransfer :: Transfer TreeShapedFact
tsTransfer = Transfer tsTransferf tsSetup tsProject tsExtend
  where
    tsTransferf _ _ _   (TsFact(TsTop,_)) = undefined
    tsTransferf p q ins (TsFact(Ts ts,stk)) = TsFact $ case ins of
      Load i       -> let k = index stk in (Ts ((k `assign` LocVar i) ts), k:stk)
      Store i      -> let k = tos   stk in pop (Ts ((LocVar i `assign` k) ts), stk) 
      Push _       -> push (Ts ts,stk)
      New _        -> push (Ts ts,stk)
      CheckCast _  -> pop (Ts ts,stk)
      Pop          -> pop (Ts ts,stk)
      IAdd         -> push $ pop2 (Ts ts,stk)
      ISub         -> push $ pop2 (Ts ts,stk)
      Goto _       -> (Ts ts,stk)
      IfFalse _    -> pop (Ts ts,stk)
      CmpEq        -> push $ pop2 (Ts ts,stk)
      CmpNeq       -> push $ pop2 (Ts ts,stk)
      ICmpGeq      -> push $ pop2 (Ts ts,stk)
      BNot         -> push $ pop (Ts ts,stk)
      BOr          -> push $ pop2 (Ts ts,stk)
      BAnd         -> push $ pop2 (Ts ts,stk)
      Return       -> undefined
      Invoke _ _   -> undefined
      GetField fn cn -> if isTreeShaped' p cn fn then (Ts $ tos stk `S.insert` ts,stk) else (Ts ts,stk)
      PutField fn cn -> case stk of
        (val :ref :_) -> pop2 $
          if tsfield || (tsval && not shares) 
            then (Ts ts,stk)
            else (Ts $ ts `S.difference` sharesWith ref (S.elems ts) q,stk)
          where
            tsfield = isTreeShaped' p cn fn
            tsval   = val `S.member` ts
            shares  = mayShareQ q val ref

    isTreeShaped' p cn fn = P.isTreeShapedType p ty
      where ty = snd . fromJust $ field p cn fn

    v `assign` w = assign' v w
    assign' v w ts
      | w `S.member` ts = v `S.insert` ts
      | otherwise       = v `S.delete` ts

    sharesWith x es q = S.fromList $ foldl k [] es
      where  k xs y = if  mayShareQ q x y then y:xs else xs

    push (Ts ts,stk) = let k = index stk in (Ts $ k `S.insert` ts, k:stk)
    pop (Ts ts,k:stk) = (Ts (k `S.delete` ts), stk)
    pop2 = pop . pop
    popN 0 = id
    popN n = popN (n-1) . pop

    tsSetup p cn mn = TsFact (ts, [])
      where
        md      = theMethod p cn mn
        nparams = length (methodParams md)
        ts      = Ts $ S.fromList [LocVar i | i <- [0..nparams]]

    tsProject _ _ _ _ nparams (TsFact (Ts ts,stk)) = TsFact (Ts ts',[])
      where
        params   = reverse $ take (nparams + 1) stk 
        locals   = [LocVar i | i <- [0..nparams]]
        ts''     = ts `S.intersection` S.fromList params
        ts'      = rename `S.map` ts''
        rename v = fromJust . lookup v $ zip params locals

    tsExtend _ _ _ nparams (TsFact(Ts ts1,stk1)) (TsFact(TsTop,[])) = 
      TsFact . push $ popN (nparams + 1) (Ts ts1,stk1)
      
    tsExtend _ q _ nparams (TsFact(Ts ts1,stk1)) (TsFact(Ts ts2,[v])) = TsFact(ts3,stk3)
      where
        params = reverse $ take (nparams + 1) stk1
        elems  = S.elems ts1
        shares = foldl (\ss var -> sharesWith var elems q `S.union` ss) S.empty params

        (ts',stk')   = (Ts $ ts1 `S.difference` shares, stk1)
        (ts'',stk'') = popN (nparams + 1) (ts',stk')
        (ts3,stk3)   = if v `S.member` ts2
                          then push (ts'',stk'') 
                          else (ts'', index stk'':stk'')

        

tsQueryV :: QueryV TreeShapedFact
tsQueryV = defaultQueryV{ isTreeShaped = tsIsTreeShaped }
  where
    tsIsTreeShaped (TsFact (TsTop,_)) _  = Just True
    tsIsTreeShaped (TsFact (Ts ts,[])) x = Just $ S.member x ts



