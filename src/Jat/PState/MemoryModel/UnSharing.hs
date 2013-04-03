{-# LANGUAGE MonadComprehensions #-}

module Jat.PState.MemoryModel.UnSharing 
  (
  UnSharing
  )
where

import Jat.JatM
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
import Jat.Utils.Pretty
import Jat.Utils.Fun
import qualified Jat.Program as P

import Data.Set.Monad (Set)
import qualified Data.Set.Monad as S

mname :: String
mname = "Jat.PState.MemoryModel.UnSharing"

merror :: String -> a
merror msg = error $ mname ++ msg

data MayShare = Int :><: Int deriving Show
data MayAlias = Int :=?: Int deriving Show
data MayGraph = NT Int deriving (Eq,Ord,Show)

instance Eq MayShare where
  (q1:><:q2) == (r1:><:r2) = (q1 == r1 && q2 == r2) || (q1 == r2 && q2 == r1)

instance Ord MayShare where
  qs `compare` rs = compare (ord qs) (ord rs)
    where ord (q1:><:q2) = if q1 > q2 then (q1,q2) else (q2,q1)

instance Pretty MayShare where
  pretty (q1:><:q2) = text $ show q1 ++ "><" ++ show q2

instance Eq MayAlias where
  (q1:=?:q2) == (r1:=?:r2) = (q1 == r1 && q2 == r2) || (q1 == r2 && q2 == r1) 

instance Ord MayAlias where
  qs `compare` rs = compare (ord qs) (ord rs)
    where ord (q1:=?:q2) = if q1 > q2 then (q1,q2) else (q2,q1)

instance Pretty MayAlias where
  pretty (q1:=?:q2) = text $ show q1 ++ "=?" ++ show q2

instance Pretty MayGraph where
  pretty (NT q) = text $ '&': show q

data UnSharing = UnSharing (S.Set MayAlias) (S.Set MayShare) (S.Set MayGraph) deriving (Eq,Ord,Show)

emptyUS :: UnSharing 
emptyUS = UnSharing S.empty S.empty S.empty

type US i = PState i UnSharing

mayShareWith :: Address -> UnSharing -> [Address]
adr `mayShareWith` (UnSharing _ ms _) = 
  [ adr'  | (adr1:><:adr2) <- S.elems ms
          , adr == adr1 || adr == adr2
          , let adr' = if adr == adr1 then adr1 else adr2]

mayAliasWith :: Address -> UnSharing -> [Address]
adr `mayAliasWith` (UnSharing ma _ _) = 
  [ adr'  | (adr1:=?:adr2) <- S.elems ma
          , adr == adr1 || adr == adr2
          , let adr' = if adr == adr1 then adr1 else adr2]

instance Pretty UnSharing where
  pretty (UnSharing ma ms mg) =
    (hsep . map pretty $ S.elems ma)
    <$> (hsep . map pretty $ S.elems ms)
    <$> (hsep . map pretty $ S.elems mg)

instance MemoryModel UnSharing where
  new       = newUS
  getField  = getFieldUS
  putField  = putFieldUS

  invoke    = invokeUS
  equals    = equalsUS
  nequals   = nequalsUS

  initMem   = initMemUS

  leq       = undefined
  join      = undefined

  state2TRS = undefined

newUS :: (Monad m, IntDomain i) => US i -> P.ClassId -> JatM m (PStep(US i))
newUS (PState hp (Frame loc stk cn mn pc :frms) us) newcn = do
  p <- getProgram
  let obt       = mkInstance p newcn
      (adr,hp') = insertHA obt hp
      stk'      = RefVal adr :stk
  return $ topEvaluation (PState hp' (Frame loc stk' cn  mn (pc+1) :frms) us)
newUS _ _ = merror ".new: unexpected case."


getFieldUS :: (Monad m, IntDomain i) => US i -> P.ClassId -> P.FieldId -> JatM m (PStep(US i))
getFieldUS st cn fn = case opstk $ frame st of
  Null :_        -> return $ topEvaluation (EState NullPointerException)
  RefVal adr : _ -> tryInstanceRefinement st adr |>> return (mkGetField st cn fn)
  _              -> error $ mname ++ ".getField: unexpected case."

putFieldUS :: (Monad m, IntDomain i) => US i -> P.ClassId -> P.FieldId -> JatM m (PStep(US i))
putFieldUS st cn fn = case opstk $ frame st of
  _ : Null       : _ -> return $ topEvaluation (EState NullPointerException)
  _ : RefVal adr : _ -> tryInstanceRefinement st adr 
                       |> tryEqualityRefinement st adr 
                       |>> mkPutField (updatePutField st) st cn fn
  _                  -> merror ".getField: unexpected case."


updatePutField :: Eq i => US i -> UnSharing
updatePutField st@(PState hp _ (UnSharing ma ms mt)) = case opstk $ frame st of
  RefVal o1 : RefVal o0 : _ -> 
    let ms' = (ms `S.union` newShares o1 o0)
        mt' = (mt `S.union` newGraphs1 o1 o0 `S.union` newGraphs2 o1 o0)
    in  UnSharing ma ms' mt'
  _                         -> merror ".updatePutfield: unexpected case."
  where
    newShares  o1 o0 = [ p:><:q | p <- o1 `annotatedWith` st , q <- o0 `reaches` st, p/=q ]
    newGraphs1 o1 o0 = [ NT p | p <- o1 `reachedBy` st, q1 <- p `reaches` st
                              , q2 <- o0 `reaches` st , q1 == q2
                              , noCommonPrefix (pathsFromTo p o1 hp) (pathsFromTo p q1 hp)]
    noCommonPrefix paths1 paths2 = not $ or [hasCommonPrefix path1 path2 | path1 <- paths1, path2 <- paths2]
    newGraphs2 o1 o0 = if hasCommonSuccessor o0 hp ||  any (\q -> NT q `S.member` mt) (reachable o0 hp)
                    then [NT p | p <- o1 `annotatedWith` st]
                    else S.empty
updatePutField _ = merror ".updatePutField: unexpected case."

annotatedWith :: Address ->  US i -> Set Address
adr `annotatedWith` st = S.fromList (adr `mayAliasWith` us) `S.union` S.fromList (adr `mayShareWith` us)
  where us = annotations st
reaches :: Address -> US i -> Set Address
adr `reaches` st = S.unions $ S.fromList reachables : map (`annotatedWith` st) reachables
  where reachables = reachable adr (heap st)
reachedBy :: Address -> US i-> Set Address
adr1 `reachedBy` st = S.fromList $ filter (\adr2 -> adr1 `S.member` (adr2 `reaches` st)) (addresses $ heap st) 


invokeUS :: (Monad m, IntDomain i) => US i -> P.MethodId -> Int -> JatM m (PStep(US i))
invokeUS st1 mn1 n1 = do
  p <- getProgram
  invoke' p st1 mn1 n1
  where
    invoke' p st@(PState hp (Frame loc stk fcn fmn pc :frms) us) mn n =
      case rv  of
        Null     -> return . topEvaluation $ EState NullPointerException
        RefVal q -> tryInstanceRefinement st q
                  |>> return (topEvaluation $ PState hp (frm:Frame loc stk2 fcn fmn pc:frms) us)
        _        -> merror ".invoke: invalid type on stack"
      where
        (ps,stk1)   = splitAt n stk
        ([rv],stk2) = splitAt 1 stk1
        cn1         = className $ lookupH (theAddress rv) hp
        (cn2,mb)    = P.seesMethodIn p cn1 mn
        mxl         = P.maxLoc mb
        frm         = Frame (initL (rv:reverse ps) mxl) [] cn2 mn 0
    invoke' _ _ _ _ = error ".inoke: exceptional case."

equalsUS :: (Monad m, IntDomain i) => US i -> JatM m (PStep(US i))
equalsUS st@(PState hp (Frame loc (v1:v2:stk) cn mn pc :frms) us@(UnSharing ma _ _)) =
  equalsx v1 v2
  where
    equalsx (RefVal q) (RefVal r) | q == r = mkBool True
    equalsx (RefVal q) (RefVal r) = 
      if (q :=?: r) `S.member` ma
        then return $ equalityRefinement st (q:=?:r)
        else mkBool False
    equalsx (RefVal q) Null =
      tryInstanceRefinement st q |>> mkBool False
    equalsx Null (RefVal r) =
      tryInstanceRefinement st r |>> mkBool False
    equalsx _ _ = merror ".equals: unexpected case."
    mkBool b = return . topEvaluation $ PState hp (Frame loc stk' cn mn (pc+1):frms) us
      where stk' = BoolVal (AD.constant b) : stk
equalsUS _ = merror ".equals: exceptional case."

nequalsUS :: (Monad m, IntDomain i) => US i -> JatM m (PStep(US i))
nequalsUS st@(PState hp (Frame loc (v1:v2:stk) cn mn pc :frms) us@(UnSharing ma _ _)) =
  nequalsx v1 v2
  where
    nequalsx (RefVal q) (RefVal r) | q == r = mkBool False
    nequalsx (RefVal q) (RefVal r) =
      if (q :=?: r) `S.member` ma
        then return $ equalityRefinement st (q:=?:r)
        else mkBool True
    nequalsx (RefVal q) Null =
      tryInstanceRefinement st q |>> mkBool True
    nequalsx Null (RefVal r) =
      tryInstanceRefinement st r |>> mkBool True
    nequalsx _ _ = merror ".nequals: unexpected case."
    mkBool b = return . topEvaluation $ PState hp (Frame loc stk' cn mn (pc+1):frms) us
      where stk' = BoolVal (AD.constant b) : stk
nequalsUS _ = merror ".nequals: exceptional case."

    
initMemUS :: (Monad m, IntDomain i) => P.ClassId -> P.MethodId -> JatM m (US i)
initMemUS cn mn = do
  p <- getProgram
  let m = P.theMethod p cn mn
  (hp1,_)      <- mkAbsInstance emptyH 0 cn
  (hp2,params) <- foldM defaultAbstrValue (hp1,[]) (P.methodParams m)
  let loc = initL params $ P.maxLoc m
  return $ PState hp2 [Frame loc [] cn mn 0] emptyUS
  where
    defaultAbstrValue (hp,params) ty = case ty of
      P.BoolType    -> AD.top >>= \b -> return (hp, params++[BoolVal b])
      P.IntType     -> AD.top >>= \i -> return (hp, params++[IntVal i])
      P.NullType    ->                  return (hp, params++[Null])
      P.Void        ->                  return (hp, params++[Unit])
      P.RefType cn' ->                  return (hp',params++[RefVal r])
        where (r, hp') = insertHA (AbsVar cn') hp

tryInstanceRefinement :: (Monad m, IntDomain i) => US i -> Address -> JatM m (Maybe (PStep(US i)))
tryInstanceRefinement st@(PState hp _ _) q = 
    tryEqualityRefinementWithInstance st q |> case lookupH q hp of
      AbsVar _     -> getProgram >>= \p -> Just `liftM` instanceRefinement p st q
      Instance _ _ -> return Nothing 
tryInstanceRefinement _ _ = merror ".tryInstanceRefinement: exceptional case."

-- o1-><-o2 : and o1 is Unknown
-- o1->1 o *<-o2
-- if o1 is refined
  -- kids could equal to o2
  -- if o2 is Instance then original annot can be removed
  -- if o2 is Abstract then annot have to be kept due to "symmetry" of -><-
instanceRefinement :: (Monad m, IntDomain i) => P.Program -> US i -> Address -> JatM m (PStep(US i))
instanceRefinement p st@(PState hp frms us) adr = do
  instances <- instancesM
  nullref   <- nullM
  return . topRefinement $ nullref:instances
  where
    cns  = P.subClassesOf p . className $ lookupH adr hp
    obtM = mapM (mkAbsInstance hp adr) cns

    instancesM = map mkInstanceM `liftM` obtM
      where mkInstanceM (hp1,obt1) = let hp2 = updateH adr obt1 hp1 in PState hp2 frms (updateSharing adr obt1 hp2 us)
    nullM      = return $ substitute (RefVal adr) Null st
    

    updateSharing :: Address -> Object i -> Heap i -> UnSharing -> UnSharing
    updateSharing adr1 obj1 hp1 us1@(UnSharing ma ms mt) =
      let ma' = ma `S.union` S.fromList newAliases1 `S.union` S.fromList newAliases2
          ms' = S.filter thefilter ms `S.union` S.fromList newSharing1 `S.union` S.fromList newSharing2
          mt' = mt `S.union` S.fromList newGraphs
      in UnSharing ma' ms' mt'
      where
        sharesWith = adr1 `mayShareWith` us1
        obtrefs    = referencesO obj1

        thefilter (ref1:><:ref2) = not $ (ref1 == adr || ref2 == adr) && isInstanceH ref1 && isInstanceH ref2 
        newAliases1 = [ newr :=?: oldr | newr <- obtrefs, oldr <- sharesWith]
        newSharing1 = [ newr :><: oldr | newr <- obtrefs, oldr <- sharesWith]
        
        (newAliases2, newSharing2, newGraphs) =
          if NT adr `S.member` mt
            then
            ( [ new1:=?:new2  | new1 <- adr:obtrefs, new2 <- obtrefs, new1 /= new2
                              , let {cn1 = classNameH new1; cn2 = classNameH new2}
                                in  cn1 `isSuper` cn2 || cn2 `isSuper` cn1]
            , [ new1:><:new2 | new1 <- adr:obtrefs, new2 <- obtrefs, new1 /= new2]
            , [ NT ref | ref <- obtrefs])
            else ([],[],[])
        classNameH cn  = className $ lookupH cn hp1
        isSuper        = P.isSuper p
        isInstanceH ref = isInstance $ lookupH ref hp1
instanceRefinement _ _ _ = merror ".instanceRefinement: unexpected case."



tryEqualityRefinement :: (Monad m, IntDomain i) => US i -> Address -> JatM m (Maybe(PStep(US i)))
tryEqualityRefinement st r =
  case anyEqualityRefinement st r of
    Just r' -> return . Just $ equalityRefinement st r'
    Nothing -> return Nothing

anyEqualityRefinement :: (IntDomain i) => US i -> Address -> Maybe MayAlias
anyEqualityRefinement (PState _ _ us) q = 
  case q `mayAliasWith` us of
   (r:_) -> Just (q:=?:r)
   []    -> Nothing
anyEqualityRefinement _ _ = merror ".anyEqualityRefinement: exceptional case."
                                                                                                                 --
-- like tryEqualityRefinement, but considers only the case if the aliased references is an instance
tryEqualityRefinementWithInstance :: (Monad m, IntDomain i) => US i -> Address -> JatM m (Maybe(PStep(US i)))
tryEqualityRefinementWithInstance st r =
  case anyEqualityRefinementWithInstance st r of
    Just r' -> return . Just $ equalityRefinement st r'
    Nothing -> return Nothing

anyEqualityRefinementWithInstance :: (IntDomain i) => US i -> Address -> Maybe MayAlias
anyEqualityRefinementWithInstance (PState hp _ ann) q = anyq aliases
  where
    aliases = q `mayAliasWith` ann
    anyq (r:rs)     = 
      case lookupH r hp of 
        Instance _ _ -> Just (q:=?:r)
        _            -> anyq rs
    anyq [] = Nothing
anyEqualityRefinementWithInstance _ _ = merror ".anyEqualityRefinementWithInstance: exceptional case."

equalityRefinement :: (IntDomain i) => US i -> MayAlias -> PStep (US i)
equalityRefinement st@(PState hp frms (UnSharing ma ms mt)) (ref1:=?:ref2) = 
  case (lookupH ref1 hp, lookupH ref2 hp) of
    (AbsVar _, _) -> topRefinement [mkEqual ref1 ref2, mkNequal]
    (_, AbsVar _) -> topRefinement [mkEqual ref2 ref1, mkNequal]
    _             -> merror ".equalityRefinement: unexpected case"
  where
    me' = (/= (ref1:=?:ref2)) `S.filter` ma
    mkEqual r1 r2 =  
      let PState hp1 fs1 (UnSharing _ ms1 mt1) = substitute (RefVal r1) (RefVal r2) st
      in  PState hp1 fs1 (UnSharing me' ms1 mt1)
    mkNequal = PState hp frms (UnSharing me' ms mt)
equalityRefinement _ _ = merror ".equalityRefinement: unexpected case."



--leq' :: IntDomain i => P.Program -> PState i UnSharing -> PState i UnSharing -> Bool
--leq' p st1 st2 | not $ isSimilar st1 st2 = False
--leq' p st1 st2 
  -- | not $ all (`elem` spaths) tpaths = False
  -- | otherwise  = and  [checkValues
                      --,checkDistinctness
                      --,checkAlias
                      --,checkMayAlias
                      --,propagateShare
                      --,checkMayShare
                      --,checkMaybeGraph
                      --,propagateGraph]
  --where
    --spaths = undefined
    --tpaths = undefined
    --checkValues = undefined
    --checkDistinctness = undefined
    --checkAlias = undefined
    --checkMayAlias = undefined
    --propagateShare = undefined
    --checkMayShare = undefined
    --checkMaybeGraph = undefined
    --propagateGraph = undefined

  













