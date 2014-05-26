{-# LANGUAGE MultiParamTypeClasses #-}
-- | Pair Sharing domain following 'Pair Sharing Analysis of Object-Oriented
-- Programs' Spoto et al.
module JFlow.PairSharing 
  (
    SharingFact
  , shFlow
  , mayShare
  , maySharesWith
  , maySharingVars 
  )
where

import Jinja.Program
import qualified Jat.PairSet as PS

import JFlow.Data

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


mayShare :: SharingFact -> Var -> Var -> Bool
mayShare (ShFact sh) x y = (x:><:y) `PS.member` sh

maySharesWith :: SharingFact -> Var -> [Var]
maySharesWith (ShFact sh) x = x `PS.pairsWith` sh

maySharingVars :: SharingFact -> [(Var,Var)]
maySharingVars (ShFact sh) = PS.toList sh

instance MayShareQ SharingFact       where mayShareQ = mayShare
instance MaySharesWithQ SharingFact  where maySharesWithQ = maySharesWith
instance MaySharingVarsQ SharingFact where maySharingVarsQ = maySharingVars

instance Pretty SharingFact where
  pretty (ShFact sh) = 
    string "ShFact"
    <$> list (map pretty (PS.elems sh :: [Share]))

instance Show SharingFact where
  show = show . pretty


shFlow :: (HasIndexQ w, HasTypeQ w) => Flow SharingFact w
shFlow = Flow shLattice shTransfer

shLattice :: SemiLattice SharingFact
shLattice = SemiLattice shName shBot shJoin
  where
    shName = "PairSharing"
    shBot  = ShFact PS.empty
    shJoin _ (ShFact sh1) (ShFact sh2) = ShFact (sh1 `PS.union` sh2)

shTransfer :: (HasIndexQ w, HasTypeQ w) => Transfer SharingFact w
shTransfer = Transfer shTransferf shSetup shProject shExtend
  where
    assign x y sh 
      | (y:><:y) `PS.member` sh' = (x:><:y) `PS.insert` (sh' `PS.union` PS.rename (y `to` x) sh')
      | otherwise                = sh'
      where 
        sh'          = x `PS.delete'` sh
        to old new z = if z == old then new else z

    normalize p w = PS.filter ty
      where ty (x:><:y) = areSharingTypes p (hasTypeQ w x) (hasTypeQ w y)

    -- index (i,j) after operation
    shTransferf p _ ins (_,w) sh = 
      let (i,j) = hasIndexQ w in shTransferf' p ins w sh i j
    shTransferf' p ins w (ShFact sh) i j = ShFact $ case ins of
      Load n          -> (StkVar i j `assign` LocVar i n) sh
      Store n         -> let (x,y) = (LocVar i n, StkVar i (j+1)) in  PS.delete' y $ (x `assign` y) sh
      Push _          -> sh
      New _           -> let x = StkVar i j in  x:><:x `PS.insert` sh
      GetField fn cn  -> if isPrimitiveType $ snd (field p cn fn) 
                          then PS.delete' (StkVar i j) sh
                          else normalize p w sh
      PutField fn cn  ->  if isPrimitiveType $ snd (field p cn fn)
                          then PS.delete' val $ PS.delete' ref sh
                          else normalize p w . PS.delete' val . PS.delete' ref $ (ref `put` val) sh
                        where (val,ref) = (StkVar i (j+2), StkVar i (j+1))
      CheckCast _     -> normalize p w sh
      Pop             -> StkVar i (j+1) `PS.delete'` sh
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

    shProject _ _ _ nparams w (ShFact sh) = ShFact (PS.renameWithLookup rename sh)
      where 
        (i,j)  = hasIndexQ w
        rename = flip lookup (zip [StkVar i k | k <- [j,j-1..]] [LocVar (i+1) k | k <- [nparams,nparams-1..0]])

    shExtend _ _ nparams w _ (ShFact sh) = 
      ShFact . PS.filter (\(x:><:y) -> k x && k y) $ (rl `assign` rs) sh
      where 
        (i,j) = hasIndexQ w
        (rs,rl) = (StkVar (i+1) 0, StkVar i (j -nparams))
        k (StkVar i2 _) = i2 <= i
        k (LocVar i2 _) = i2 <= i

--shQueryV :: QueryV SharingFact
--shQueryV = defaultQueryV {mayShare = shMayShare, maySharesWith = shMaySharesWith}
  --where 
    --shMayShare      (ShFact sh) x y = Just $ (x:><:y) `PS.member` sh
    --shMaySharesWith (ShFact sh) x   = Just $ x `PS.pairsWith` sh


