{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Jat.PState.MemoryModel.PairSharing
  (
  PairSharing
  )
where

import qualified Control.Applicative as A

import Jat.Constraints (PATerm)
import Jat.JatM
import qualified Jat.PairSet as PS
import Jat.PState.AbstrValue
import Jat.PState.AbstrDomain as AD
import Jat.PState.Data
import Jat.PState.Fun
import Jat.PState.Frame
import Jat.PState.Heap
import Jat.PState.IntDomain
import Jat.PState.MemoryModel.Data
import Jat.PState.Object
import Jat.PState.Step
import Jat.Utils.Pretty as PP
import Jat.Utils.Fun
import qualified Jinja.Program as P

import Data.Maybe ( fromMaybe)
import qualified Data.Map as M
import Control.Monad.State
import Data.List (find)
import Data.Array as A

import qualified JFlow.Instances as F
import qualified JFlow.Flow as F

-- import Debug.Trace

mname :: String
mname = "Jat.PState.MemoryModel.PairSharing"

merror :: String -> a
merror msg = error $ mname ++ msg

data NShare = Address :/=: Address deriving (Eq,Ord)

type NShares = PS.PairSet Address

instance PS.Pair NShare Address where
  unview (a:/=:b) = (a,b)
  view            = uncurry (:/=:)

instance Pretty NShare where pretty (q:/=:r) = int q <> text "/=" <> int r
instance Show NShare   where show = show . pretty

data PairSharing = 
  Sh NShares (F.FactBase F.PFactP) ([F.Facts F.PFactP]) F.PFactP
type Sh i = PState i PairSharing

instance Pretty PairSharing where 
  pretty sh@(Sh _ _ _ f) =
    hsep (map pretty $ nShares' sh) PP.<$>
    string ( show f)

instance Show PairSharing where show = show . pretty

liftSh :: (PairSharing -> PairSharing) -> Sh i -> Sh i
liftSh f (PState hp frms sh) = PState hp frms (f sh)
liftSh _ st                  = st

nShares :: PairSharing -> NShares
nShares (Sh ns _ _ _) = ns

nShares' :: PairSharing -> [NShare]
nShares' = PS.elems . nShares

fact :: PairSharing -> F.PFactP
fact (Sh _ _ _ f) = f


liftNS :: (NShares -> NShares) -> PairSharing -> PairSharing
liftNS g (Sh ns fb fs f) = Sh (g ns) fb fs f

liftNS' :: (NShares -> a) -> PairSharing -> a
liftNS' f = f . nShares


initSh :: P.Program -> P.ClassId -> P.MethodId -> PairSharing
--initSh p cn mn = trace (show (fs,fb)) $ Sh PS.empty fb [fs] (F.unFacts fs A.! 0)
initSh p cn mn = Sh PS.empty fb [fs] (F.unFacts fs A.! 0)
  where (fs,fb) = F.analyse (F.pFlowP p) p cn mn

sharing :: Sh i -> PairSharing
sharing (PState _ _ sh) = sh
sharing _               = error "Jat.PState.MemoryModel.PairSharing.sharing: the impossible happened"


-- properties
isAcyclicType :: P.Program -> Sh i -> Address -> Bool
isAcyclicType p st = P.isAcyclicClass p . refKindOf st

acyclicSh :: Sh i -> Address -> Bool
acyclicSh st q = any k (F.acyclicVarsP . fact $ sharing st)
  where k x = q `elem` reachableV x st

acyclic :: P.Program -> Sh i -> Address -> Bool
acyclic p st q = isAcyclicType p st q || acyclicSh st q


areSharingTypes :: P.Program -> Sh i -> Address -> Address -> Bool
areSharingTypes p st q r = P.areSharingClasses p (refKindOf st q) (refKindOf st r)

maybeSharesSh :: Sh i -> Address -> Address -> Bool
maybeSharesSh st q r = any pairShares (F.sharingVarsP . fact $ sharing st)
  where
    pairShares (x,y) =
      (q `elem` xReaches && r `elem` yReaches) ||
      (q `elem` yReaches && r `elem` xReaches)
      where
        xReaches = reachableV x st
        yReaches = reachableV y st

maybeShares :: P.Program -> Sh i -> Address -> Address -> Bool
maybeShares p st q r = areSharingTypes p st q r && maybeSharesSh st q r


areReachingTypes :: P.Program -> Sh i -> Address -> Address -> Bool
areReachingTypes p st q r = P.areReachingClasses p (refKindOf st q) (refKindOf st r)

maybeReachesSh :: P.Program -> Sh i -> Address -> Address -> Bool
maybeReachesSh p st q r = 
  any pairReaches (F.reachingVarsP . fact $ sharing st)
  && if q `elem` reachable r (heap st) then not (acyclic p st q) else True -- TODO: is this sound (necessary for flatten example)
  where pairReaches (x,y) = q `elem` reachableV x st && r `elem` reachableV y st

maybeReaches :: P.Program -> Sh i -> Address -> Address -> Bool
maybeReaches p st q r = areReachingTypes p st q r && maybeReachesSh p st q r


isValidStateAC :: Sh i -> Bool
isValidStateAC st@(PState hp _ _) = not $ any (acyclicSh st) nonac
  where nonac = (`isCyclic` hp) `filter` addresses hp
isValidStateAC _ = True

--maybeSharesV :: P.Program -> Sh i -> P.Var -> P.Var -> Bool
--maybeSharesV p st x y =
  --P.areSharingTypes p (typeV x st) (typeV y st) &&
  --order (x,y) `elem` (F.sharingVars . fact $ sharing st)
  --where order (v,w) = if v <= w then (v,w) else (w,v)

unShare :: P.Program -> [Address] -> [Address] -> Sh i -> Sh i
unShare p qs rs st@(PState hp frms sh) = 
  PState hp frms (PS.union elements `liftNS` sh)
  where 
    elements    = PS.fromList [ q:/=:r | q <- qs, r <- rs, q /= r, related q r ]
    related q r = P.areRelatedTypes p (tyOf st q) (tyOf st r)
unShare _ _ _ _ = error "Jat.PState.MemoryModel.PairSharingunShare: the impossible happened"

updateSH :: P.Program -> P.PC -> P.Instruction -> Sh i -> Sh i
updateSH _ _ _ st@(PState _ [] _) = st
updateSH _ _ ins st@(PState hp frms (Sh ns fb (fs:fss) _)) = case ins of 
  P.Return -> PState hp frms (Sh ns fb fss f1)
  _        -> PState hp frms (Sh ns fb (fs:fss) f2)
  where
    pc = pcounter $ frame st
    f1 = F.unFacts (head fss) A.! pc
    f2 = F.unFacts fs A.!pc
updateSH _ _ _ st = st

instance MemoryModel PairSharing where
  new       = newSH
  getField  = getFieldSH
  putField  = putFieldSH

  invoke    = invokeSH
  equals    = equalsSH
  nequals   = nequalsSH

  initMem   = initMemSH

  leq       = leqSH
  lub       = joinSH

  normalize = normalizeSH
  state2TRS = state2TRSSH

  update    = updateSH
  

newSH :: (Monad m, IntDomain i) => Sh i -> P.ClassId -> JatM m (PStep(Sh i))
newSH (PState hp (Frame loc stk cn mn pc :frms) sh) newcn = do
  p <- getProgram
  let obt       = mkInstance p newcn
      (adr,hp') = insertHA obt hp
      stk'      = RefVal adr :stk
      st1       = PState hp' (Frame loc stk' cn mn (pc+1) :frms) sh
      st2       = unShare p [adr] (addresses hp) st1
  return $ topEvaluation st2
newSH _ _ = merror ".new: unexpected case."

getFieldSH :: (Monad m, IntDomain i) => Sh i -> P.ClassId -> P.FieldId -> JatM m (PStep(Sh i))
getFieldSH st cn fn = case opstk $ frame st of
  Null :_         -> return $ topEvaluation (EState NullPointerException)
  RefVal adr : _  -> tryInstanceRefinement st adr |>> return (mkGetField st cn fn)
  _               -> error $ mname ++ ".getField: unexpected case."


putFieldSH :: (Monad m, IntDomain i) => Sh i -> P.ClassId -> P.FieldId -> JatM m (PStep(Sh i))
putFieldSH st@PState{} cn fn = case opstk $ frame st of
  _ : Null       : _ -> return $ topEvaluation (EState NullPointerException)
  _ : RefVal adr : _ -> tryInstanceRefinement st adr
                       |> tryEqualityRefinement st adr
                       |>> do
                       stp1 <- mkPutField (sharing st) st cn fn
                       return $ case stp1 of
                          Evaluation (st1,con) -> 
                            let st2 = updateSH undefined undefined (P.PutField fn cn) st1 in
                            if isValidStateAC st2
                              then Evaluation (normalize st2,con) 
                              else topEvaluation $ EState IllegalStateException
                          stp -> stp
  _                  -> merror ".getField: unexpected case."
putFieldSH _ _ _ = error "Jat.PState.MemoryModel.PairSharing.putFieldSH: the impossible happened"


invokeSH :: (Monad m, IntDomain i) => Sh i -> P.MethodId -> Int -> JatM m (PStep(Sh i))
invokeSH st1 mn1 n1 = do
  p <- getProgram
  invoke' p st1 mn1 n1
  where
    invoke' p st@(PState hp (Frame loc stk fcn fmn pc :frms) (Sh ns fb fs f)) mn n =
      case rv  of
        Null     -> return . topEvaluation $ EState NullPointerException
        RefVal q -> tryInstanceRefinement st q
                  |>> return (topEvaluation $ PState hp (frm:Frame loc stk2 fcn fmn pc:frms) sh')
        _        -> merror ".invoke: invalid type on stack"
      where
        (ps,stk1)   = splitAt n stk
        ([rv],stk2) = splitAt 1 stk1
        cn1         = className $ lookupH (theAddress rv) hp
        (cn2,mb)    = P.seesMethodIn p cn1 mn
        mxl         = P.maxLoc mb
        frm         = Frame (initL (rv:reverse ps) mxl) [] cn2 mn 0
        fs'         = F.queryFB'' (programLocation st) cn2 mn f fb 
        sh'         = Sh ns fb (fs':fs) (F.unFacts fs' A.! 0)
    invoke' _ _ _ _ = error ".inoke: exceptional case."

tryInstanceRefinement :: (Monad m, IntDomain i) => Sh i -> Address -> JatM m (Maybe (PStep(Sh i)))
tryInstanceRefinement st@(PState hp _ _) q = case lookupH q hp of
    AbsVar _     -> getProgram >>= \p -> Just `liftM` instanceRefinement p st q
    Instance _ _ -> return Nothing
tryInstanceRefinement _ _ = merror ".tryInstanceRefinement: exceptional case."

instanceRefinement :: (Monad m, IntDomain i) => P.Program -> Sh i -> Address -> JatM m (PStep(Sh i))
instanceRefinement p st@(PState hp frms sh) adr = do
  instances <- instancesM
  nullref   <- nullM
  return . topRefinement $ nullref:instances
  where
    cns  = P.subClassesOf p . className $ lookupH adr hp
    obtM = mapM (mkAbsInstance hp adr) cns

    instancesM = map mkInstanceM `liftM` obtM
      where mkInstanceM (hp1,obt1) = let hp2 = updateH adr obt1 hp1 in PState hp2 frms sh
    nullM      = return $ substituteSh st
    substituteSh st1 = liftNS (PS.delete' adr) `liftSh` substitute (RefVal adr) Null st1
instanceRefinement _ _ _ = error "Jat.PState.MemoryModel.PairSharing.instanceRefinement: the impossible happened"

tryEqualityRefinement :: (Monad m, IntDomain i) => Sh i -> Address -> JatM m (Maybe(PStep(Sh i)))
tryEqualityRefinement st@(PState hp _ _) q = do
  p <- getProgram
  case find (maybeEqual p st q) (addresses hp) of
    Just r  -> Just `liftM` equalityRefinement st q r
    Nothing -> return Nothing
tryEqualityRefinement _ _ = error "Jat.PState.MemoryModel.PairSharing.tryEqualityRefinement: the impossible happened"

-- rename also TreeShaped q
equalityRefinement :: (Monad m, IntDomain i) => Sh i -> Address -> Address -> JatM m (PStep(Sh i))
equalityRefinement st@(PState hp frms sh) q r = do
  p <- getProgram
  return . topRefinement $ if isValidStateAC mkEqual && leqSH p mkEqual st then [mkEqual, mkNequal] else [mkNequal]
  where
    mkEqual  = liftNS (PS.renameWithLookup (`lookup` [(r,q)]))`liftSh` substitute (RefVal r) (RefVal q) st
    mkNequal = PState hp frms (PS.insert (r:/=:q) `liftNS` sh)
equalityRefinement _ _ _ = error "Jat.PState.MemoryModel.PairSharing.equalityRefinement: the impossible happened"

maybeEqual :: IntDomain i => P.Program -> Sh i -> Address -> Address -> Bool
maybeEqual p st q r = 
  q/=r                                          && 
  not (PS.member (q:/=:r) `liftNS'` sharing st) && 
  maybeShares p st q r

equalsSH :: (Monad m, IntDomain i) => Sh i -> JatM m (PStep(Sh i))
equalsSH st@(PState hp (Frame loc (v1:v2:stk) cn mn pc :frms) sh) =
  getProgram >>= \p -> equalsx p v1 v2
  where
    equalsx _ (RefVal q) (RefVal r) | q == r = mkBool True
    equalsx _ (RefVal q) (RefVal r) | PS.member (q:/=:r) `liftNS'` sh = mkBool False
    equalsx p (RefVal q) (RefVal r) =
      if maybeEqual p st q r
         then equalityRefinement st q r
         else mkBool False
    equalsx _ (RefVal q) Null =
      tryInstanceRefinement st q |>> mkBool False
    equalsx _ Null (RefVal r) =
      tryInstanceRefinement st r |>> mkBool False
    equalsx _ _ _ = merror ".equals: unexpected case."
    mkBool b = return . topEvaluation $ PState hp (Frame loc stk' cn mn (pc+1):frms) sh
      where stk' = BoolVal (AD.constant b) : stk
equalsSH _ = merror ".equals: exceptional case."

nequalsSH :: (Monad m, IntDomain i) => Sh i -> JatM m (PStep(Sh i))
nequalsSH st@(PState hp (Frame loc (v1:v2:stk) cn mn pc :frms) sh) =
  getProgram >>= \p -> nequalsx p v1 v2
  where
    nequalsx _ (RefVal q) (RefVal r) | q == r = mkBool False
    nequalsx _ (RefVal q) (RefVal r) | PS.member (q:/=:r) `liftNS'` sh = mkBool True
    nequalsx p (RefVal q) (RefVal r) =
      if maybeEqual p st q r
         then equalityRefinement st q r
         else mkBool True
    nequalsx _ (RefVal q) Null =
      tryInstanceRefinement st q |>> mkBool True
    nequalsx _ Null (RefVal r) =
      tryInstanceRefinement st r |>> mkBool True
    nequalsx _ _ _ = merror ".nequals: unexpected case."
    mkBool b = return . topEvaluation $ PState hp (Frame loc stk' cn mn (pc+1):frms) sh
      where stk' = BoolVal (AD.constant b) : stk
nequalsSH _ = merror ".nequals: exceptional case."

initMemSH :: (Monad m, IntDomain i) => P.ClassId -> P.MethodId -> JatM m (Sh i)
initMemSH cn mn = do
  p <- getProgram
  let m = P.theMethod p cn mn
  (hp1,_)      <- mkAbsInstance emptyH 0 cn
  (hp2,params) <- foldM defaultAbstrValue (hp1,[]) (P.methodParams m)
  let loc = initL (RefVal 0:params) $ P.maxLoc m
      as  = addresses hp2
      st1 = PState hp2 [Frame loc [] cn mn 0] (initSh p cn mn)
      st2 = unShare p as as st1
  return st2
  where
    defaultAbstrValue (hp,params) ty = case ty of
      P.BoolType    -> AD.top >>= \b -> return (hp, params++[BoolVal b])
      P.IntType     -> AD.top >>= \i -> return (hp, params++[IntVal i])
      P.NullType    ->                  return (hp, params++[Null])
      P.Void        ->                  return (hp, params++[Unit])
      P.RefType cn' ->                  return (hp',params++[RefVal r])
        where (r, hp') = insertHA (AbsVar cn') hp

newtype M i = M {  
    unMorph      :: M.Map (AbstrValue i) (AbstrValue i)
  }
type Morph i = State (M i)

emptyMorph :: M i
emptyMorph = M{unMorph=M.empty}

{-withMorph :: (M.Map Address Address -> M.Map Address Address) -> Morph a -> Morph a-}
{-withMorph f = withState (\x -> x{unMorph=f(unMorph x)})-}

modifyMorph :: (M.Map (AbstrValue i) (AbstrValue i) -> M.Map (AbstrValue i) (AbstrValue i)) -> Morph i ()
modifyMorph f = modify $ \x -> x{unMorph=f(unMorph x)}

leqSh1 :: (AbstrValue i -> Maybe (AbstrValue i)) -> PairSharing -> PairSharing -> Bool
leqSh1 lookup' sh1 sh2 =
  ns2' `PS.isSubsetOf` nShares sh1
  where
    ns2' = PS.fold k PS.empty (nShares sh2)
    k (q:/=:r) = case (lookup' (RefVal q), lookup' (RefVal r)) of
      (Just (RefVal q'), Just (RefVal r')) -> PS.insert (q':/=:r') 
      _                  -> id
    

-- leqSH tries to find a mapping from addresses/variables to values, performing a 'parallel' preorder traversal, respecting the instance relation
-- difference to definition 5.4:
-- all null values have distinct implicit references in 5.4
-- nevertheless it's fine if (references of) class variables are mapped to multiple null values
-- ie t(cn_1,cn_1) [c_1 -> null] = t(null,null) as desired
leqSH :: IntDomain i => P.Program -> Sh i -> Sh i -> Bool
leqSH p (PState hp1 frms1 sh1) (PState hp2 frms2 sh2) =
  let (leqFrms,morph) = runState runFrms emptyMorph in
  let b1 = leqFrms
      b2 = leqSh1 (flip M.lookup $ unMorph morph) sh1 sh2
  in  b1 && b2
  where
    runFrms = and `liftM` zipWithM leqValM (concatMap elemsF frms1) (concatMap elemsF frms2)

    {-leqValM :: AbstrValue i -> AbstrValue i -> Morph i Bool-}
    leqValM Unit _                  = return True
    leqValM Null Null               = return True
    leqValM (BoolVal a) (BoolVal b) | isConstant b = return $ a == b
    leqValM (IntVal i)  (IntVal j)  | isConstant j = return $ i == j

    leqValM Null v2@(RefVal r)
      | not (isInstance (lookupH r hp2)) = fromMaybe True `liftM` validMapping v2 Null

    -- liftM2 is strict in the first component !
    leqValM v1@(RefVal q) v2@(RefVal r) = do 
      bM <- validMapping v2 v1
      case bM of
        Just b  -> return b
        Nothing -> leqObjM (lookupH q hp1) (lookupH r hp2)

    leqValM v1@(BoolVal a) v2@(BoolVal b) = fromMaybe (a `AD.leq` b) `liftM` validMapping v2 v1
    leqValM v1@(IntVal i)  v2@(IntVal j)  = fromMaybe (i `AD.leq` j) `liftM` validMapping v2 v1
    leqValM _ _                           = return False

    {-validMapping :: AbstrValue i -> AbstrValue i -> Morph i (Maybe Bool)-}
    validMapping v2 v1 = do
      mapping <- gets unMorph
      case M.lookup v2 mapping of
        Just v1'-> return $ Just (v1 == v1')
        Nothing -> modifyMorph (M.insert v2 v1) >> return Nothing

    {-leqObjM :: Object i -> Object i -> Morph i Bool-}
    leqObjM (Instance cn ft) (Instance cn' ft') = (cn == cn' &&) `liftM`  leqFtM ft ft'
    leqObjM (Instance cn _) (AbsVar cn')        = return $ P.isSuber p cn cn'
    leqObjM (AbsVar cn) (AbsVar cn')            = return $ P.isSuber p cn cn'
    leqObjM _ _                                 = return False

    {-leqFtM :: FieldTable i -> FieldTable i -> Morph i Bool-}
    leqFtM ft ft' = and `liftM` zipWithM leqValM (elemsFT ft) (elemsFT ft')
leqSH _ _ _ = error "Jat.PState.MemoryModel.PairSharing.leqSH: the impossible happened"

-- Todo: take correlation into account
joinSH :: (Monad m, IntDomain i) => Sh i -> Sh i -> JatM m (Sh i)
joinSH st1@(PState _ _ sh1) st2@(PState _ _ sh2) = do
  p <- getProgram
  ~(PState hp frms _, cor)  <- mergeStates' p st1 st2 undefined
  let ns = joinNS hp cor (nShares sh1) (nShares sh2)
  {-let ns = joinNS cor (PS.empty) (PS.empty)-}
      {-ns = PS.empty-}
      sh = sharing st1
  return $ PState hp frms (const ns `liftNS` sh)
  where
    joinNS hp cor ns1 ns2 = PS.fromList $ do
      let
        (lk1,lk2) = unzip [ ((r,p),(r,q)) | (C p q, r) <-  M.toList cor ]
        qs        = addresses hp
      q1 <- qs
      q2 <- qs
      guard $ q1 < q2
      guard $ maybe False (`PS.member` ns1) ((:/=:) A.<$> lookup q1 lk1 A.<*> lookup q2 lk1)
      guard $ maybe False (`PS.member` ns2) ((:/=:) A.<$> lookup q1 lk2 A.<*> lookup q2 lk2)
      return $ q1 :/=: q2
joinSH _ _ = error "Jat.PState.MemoryModel.PairSharing.joinSH: the impossible happened"


state2TRSSH :: (Monad m, IntDomain i) => Maybe Address -> Side -> Sh i -> Sh i -> Int -> JatM m PATerm
state2TRSSH m side st1@PState{} st2@PState{} n = 
  getProgram >>= \p -> pState2TRS (isSpecial p) (maybeReaches' p) m side st2 n
  where
    {-isSpecial p adr = isCyclic adr hp || isNotTreeShaped  adr hp || not (treeShaped p st adr)-}
    isSpecial p adr = not (acyclic p st2 adr)
    maybeReaches' p q r = case lookupH q (heap st1) of
      (AbsVar _) -> maybeReaches p st1 q r
      _          -> False
state2TRSSH m side _ st n = pState2TRS undefined undefined m side st n

normalizeSH :: Sh i -> Sh i
normalizeSH (PState hp frms sh) = PState hp' frms (const (PS.filter k $ nShares sh) `liftNS` sh)
   where
     refsFS = [ r | RefVal r <- concatMap elemsF frms]
     hp'    = normalizeH refsFS hp
     refsH  = addresses hp'
     k (q:/=:r) = q `elem` refsH && r `elem` refsH
normalizeSH st = st

