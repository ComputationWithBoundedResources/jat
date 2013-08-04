{-# LANGUAGE MultiParamTypeClasses #-}
-- | Pair Sharing domain following 'Pair Sharing Analysis of Object-Oriented
-- Programs' Spoto et al.
module Jsat.PairSharing2 where

import Jat.Program
import qualified Jat.PairSet as PS

import Jsat.Data

import Text.PrettyPrint.ANSI.Leijen
{-import Debug.Trace-}



-- pair sharing domain sh:
-- (v1,v2) in sh => v1 and v2 may have a commen descendent
-- (v1,v1) not in sh => v1 is null
-- 
-- sharing happens only in 
-- variable assignments: v := w
--- (w,w) in sh   : sh|-v + (v,w) + if (w,x) in sh then (v,x) in sh
--- otherwise     : sh|-v
-- field    assignments: v := w.f
--- (w,w) in sh : sh|-v + (v,w) + if (w,x) in sh and exists common (static-descendent) type (t(w.f),t(x)) then (v,x) in sh
--- othersise   : sh|-v
-- methods

 
-- moving from denotial to operational semantics
-- we treat operand stack as temporal variables ie. Load i -> l_n := i 
-- v := exp and v.f := exp reduces to v := w and v.f = w

-- local vars are identified by their indices
-- stack vars are treated as temporary variables (loading 
--- kept as stack as ususal
--- identified by a unique negative index
--- only stack vars which are on the stack may occur in sh

data Share = Var:><:Var deriving (Eq,Ord)

instance Pretty Share where
  pretty (x:><:y) = pretty x <> text "><" <> pretty y

instance Show Share where
  show = show . pretty

instance PS.Pair Share Var where
  view            = uncurry (:><:)
  unview (x:><:y) = (x,y)

type Sharing = PS.PairSet Var


newtype SharingFact = ShFact Sharing  deriving (Eq,Ord)

instance Pretty SharingFact where
  pretty (ShFact sh) = 
    string "ShFact"
    <$> list (map pretty (PS.elems sh :: [Share]))

instance Show SharingFact where
  show = show . pretty


shFlow :: Flow SharingFact
shFlow = Flow shLattice shTransfer shQueryV

shLattice :: SemiLattice SharingFact
shLattice = SemiLattice shName shBot shJoin
  where
    shName = "PairSharing"
    shBot  = ShFact PS.empty
    shJoin _ (ShFact sh1) (ShFact sh2) = ShFact (sh1 `PS.union` sh2)

shTransfer :: Transfer SharingFact
shTransfer = Transfer shTransferf shSetup shProject shExtend
  where
    assign x y sh 
      | (y:><:y) `PS.member` sh' = (x:><:y) `PS.insert` (sh' `PS.union` PS.rename (y `to` x) sh')
      | otherwise                = sh'
      where 
        sh'          = x `PS.delete'` sh
        to old new z = if z == old then new else z

    normalize p q = PS.filter ty
      where ty (x:><:y) = areSharingTypes p (hasTypeQ q x) (hasTypeQ q y)

    -- index (i,j) after operation
    shTransferf p q ins sh = 
      let (i,j) = hasIndexQ q in shTransferf' p q ins sh i j
    shTransferf' p q ins (ShFact sh) i j = ShFact $ case ins of
      Load n          -> (StkVar i j `assign` LocVar i n) sh
      Store n         -> let (x,y) = (LocVar i n, StkVar i (j+1)) in  PS.delete' y $ (x `assign` y) sh
      Push _          -> sh
      New _           -> let x = StkVar i j in  x:><:x `PS.insert` sh
      GetField fn cn  -> if isPrimitiveType $ snd (field p cn fn) 
                          then PS.delete' (StkVar i j) sh
                          else normalize p q sh
      PutField fn cn  ->  if isPrimitiveType $ snd (field p cn fn)
                          then PS.delete' val $ PS.delete' ref sh
                          else normalize p q . PS.delete' val . PS.delete' ref $ (ref `put` val) sh
                        where (val,ref) = (StkVar i (j+2), StkVar i (j+1))
      CheckCast _     -> normalize p q sh
      Pop             -> StkVar i j `PS.delete'` sh
      IAdd            -> sh
      ISub            -> sh
      Goto _          -> sh
      IfFalse _       -> sh
      CmpEq           -> StkVar i (j+1) `PS.delete'` (StkVar i j `PS.delete'` sh)
      CmpNeq          -> StkVar i (j+1) `PS.delete'` (StkVar i j `PS.delete'` sh)
      ICmpGeq         -> sh
      BNot            -> sh
      BOr             -> sh
      BAnd            -> sh
      Return          -> undefined
      Invoke _ _      -> undefined

    put ref val sh
      | ref:><:ref `PS.member` sh = PS.closure [ref] . PS.delete' val . PS.closure [val] $ ref:><:val `PS.insert` sh
      | otherwise                 = val `PS.delete'` sh

    shSetup p cn mn = ShFact sh
      where
        md     = theMethod p cn mn
        params = zip [1..] (methodParams md)
        sh     = PS.fromList $ (LocVar 0 0:><:LocVar 0 0) : [LocVar 0 i:><:LocVar 0 i | (i, RefType _) <- params]

    shProject _ q _ _ nparams (ShFact sh) = ShFact (PS.renameWithLookup rename sh)
      where 
        (i,j)  = hasIndexQ q
        rename = flip lookup (zip [StkVar i k | k <- [j,j-1..]] [LocVar (i+1) k | k <- [nparams,nparams-1..0]])

    shExtend _ q _ nparams _ (ShFact sh) = 
      ShFact . PS.filter (\(x:><:y) -> k x && k y) $ (rl `assign` rs) sh
      where 
        (i,j) = hasIndexQ q
        (rs,rl) = (StkVar (i+1) 0, StkVar i (j -nparams))
        k (StkVar i2 _) = i2 <= i
        k (LocVar i2 _) = i2 <= i

shQueryV :: QueryV SharingFact
shQueryV = defaultQueryV {mayShare = shMayShare}
  where shMayShare (ShFact sh) x y = Just $ (x:><:y) `PS.member` sh


