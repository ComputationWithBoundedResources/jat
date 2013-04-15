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

import qualified Data.Rewriting.Term as TRS (Term (..)) 

import Data.Set.Monad (Set)
import qualified Data.Set.Monad as S
import Control.Monad (guard)
import Data.Maybe (isJust,fromJust)
import Debug.Trace

mname :: String
mname = "Jat.PState.MemoryModel.UnSharing"

merror :: String -> a
merror msg = error $ mname ++ msg

-- TODO: 
-- define `safe` member, adding and union functions
-- a :><: a | a == a should never be a member
-- take types into account:
-- =? wrt to inheritance relation
-- >< wrt to reachable classes
-- define path to return (value, path) pairs
-- add directed sharing check for putfield refinement

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

nullify :: Address -> UnSharing -> UnSharing
nullify q (UnSharing ma ms mt) = 
  let ma' = (\(q1:=?:q2) -> not (q == q1 || q == q2)) `S.filter` ma
      ms' = (\(q1:><:q2) -> not (q == q1 || q == q2)) `S.filter` ms
      mt' = (\(NT q1) -> q /= q1) `S.filter` mt
  in  UnSharing ma' ms' mt'

--nullify2 :: Address -> Address -> UnSharing -> UnSharing
--nullify2 q r (UnSharing ma ms mt) = 
  --let ma' = (/= q:=?:r) `S.filter` ma
      --ms' = (/= q:><:r) `S.filter` ms
      --mt' = (\(NT q1) -> q1 /= q && q1 /= q) `S.filter` mt
  --in  UnSharing ma' ms' mt'

--mapValuesUS :: (AbstrValue i -> AbstrValue i) -> (Address -> Address) -> US i -> US i
--mapValuesUS f1 f2 (PState hp frms (UnSharing ma ms mt)) =
  --let hp'   = mapValuesH f1 hp
      --frms' = mapValuesFS f1 frms
      --us'   = UnSharing (fmap (mamap f2) ma) (fmap (msmap f2) ms) (fmap (mtmap f2) mt)
  --in  PState hp' frms' us'
  --where
    --mamap f (q:=?:r) = f q:=?:f r
    --msmap f (q:><:r) = f q:><:f r
    --mtmap f (NT q) = NT (f q)
--mapValuesUS _ _ st  = st

substituteUS :: Eq i => AbstrValue i -> AbstrValue i -> US i -> US i
substituteUS v1 v2 st = case v1 of
  RefVal q -> mapAnnotations (nullify q) $ substitute v1 v2 st
  _        -> substitute v1 v2 st

-- Notes:
-- annotations are not transitivve , i.e. 1=?2 1=?3 does note imply 2=?3 
-- terefore substituteion does note update the values

mayShareWith :: Address -> UnSharing -> [Address]
adr `mayShareWith` (UnSharing _ ms _) = 
  [ adr'  | (adr1:><:adr2) <- S.elems ms
          , adr == adr1 || adr == adr2
          , adr1 /= adr2
          , let adr' = if adr == adr1 then adr2 else adr1]

mayAliasWith :: Address -> UnSharing -> [Address]
adr `mayAliasWith` (UnSharing ma _ _) = 
  [ adr'  | (adr1:=?:adr2) <- S.elems ma
          , adr == adr1 || adr == adr2
          , adr1 /= adr2
          , let adr' = if adr == adr1 then adr2 else adr1]

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

  leq       = leqUS
  join      = joinUS

  normalize = normalizeUS
  state2TRS = state2TRSUS

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
                       |>> liftPStep normalizeUS `liftM` mkPutField (updatePutField st) st cn fn
  _                  -> merror ".getField: unexpected case."


updatePutField :: Eq i => US i -> UnSharing
updatePutField st@(PState hp _ (UnSharing ma ms mt)) = case opstk $ frame st of
  RefVal o0 : RefVal o1 : _ -> 
    let ms' = (ms `S.union` newShares o0 o1)
        mt' = (mt `S.union` ((\a -> not $ a `S.member` noGraphs1 o0 o1) `S.filter` newGraphs1 o0 o1) `S.union` newGraphs2 o0 o1)
    in  UnSharing ma ms' mt'
  _                         -> merror ".updatePutfield: unexpected case."
  where
    newShares  o0 o1 = [ p:><:q | p <- o1 `annotatedWith` st , q <- o0 `reaches` st, p/=q ]
    noGraphs1  o0 o1 = [ NT p | p <- o1 `reachedDirectBy` st, q1 <- p `reachesDirect` st
                              , q2 <- o0 `reachesDirect` st , q1 == q2
                              , noCommonPrefix (pathsFromTo p o1 hp) (pathsFromTo p q1 hp)]
    newGraphs1 o0 o1 = [ NT p | p <- o1 `reachedBy` st, q1 <- p `reaches` st
                              , q2 <- o0 `reaches` st , q1 == q2
                              , noCommonPrefix (pathsFromTo p o1 hp) (pathsFromTo p q1 hp)]

    noCommonPrefix paths1 paths2 = not $ or [ hasCommonPrefix path1 path2 | path1 <- paths1, path2 <- paths2]
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
adr1 `reachedBy` st = 
  S.fromList $ filter (\adr2 -> adr1 `S.member` (adr2 `reaches` st)) (addresses $ heap st)

reachesDirect :: Address -> US i -> Set Address
adr `reachesDirect` st = S.fromList $ reachable adr (heap st)

reachedDirectBy :: Address -> US i-> Set Address
adr1 `reachedDirectBy` st = 
  S.fromList $ filter (\adr2 -> adr1 `S.member` (adr2 `reachesDirect` st)) (addresses $ heap st)


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
  let loc = initL (RefVal 0:params) $ P.maxLoc m
  return $ PState (trace (show $ pretty hp2) hp2) [Frame loc [] cn mn 0] emptyUS
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
  return . topRefinement $ map normalizeUS $ nullref:instances
  where
    cns  = P.subClassesOf p . className $ lookupH adr hp
    obtM = mapM (mkAbsInstance hp adr) cns

    instancesM = map mkInstanceM `liftM` obtM
      where mkInstanceM (hp1,obt1) = let hp2 = updateH adr obt1 hp1 in PState hp2 frms (updateSharing adr obt1 hp2 us)
    nullM      = return $ substituteUS (RefVal adr) Null st
    

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
        newAliases1 = [ newr :=?: oldr | newr <- obtrefs, oldr <- sharesWith, newr `isRelativeH` oldr]
        newSharing1 = [ newr :><: oldr | newr <- obtrefs, oldr <- sharesWith]
        
        (newAliases2, newSharing2, newGraphs) =
          if NT adr `S.member` mt
            then
            ( [ new1:=?:new2  | new1 <- adr:obtrefs, new2 <- obtrefs, new1 /= new2
                              , new1 `isRelativeH` new2]
            , [ new1:><:new2 | new1 <- adr:obtrefs, new2 <- obtrefs, new1 /= new2]
            , [ NT ref | ref <- obtrefs])
            else ([],[],[])
        classNameH cn  = className $ lookupH cn hp1
        isRelativeH ref1 ref2 = P.isSuper p cn1 cn2 || P.isSuper p cn2 cn1
          where (cn1,cn2) = (classNameH ref1, classNameH ref2)
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
    aliases = let qs = q `mayAliasWith` ann in trace ("ALIASES:" ++ show (q,qs)) qs
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
    mkEqual r1 r2 = substituteUS (RefVal r1) (RefVal r2) st
    mkNequal = PState hp frms (UnSharing ((/= ref1:=?:ref2) `S.filter` ma) ms mt)
equalityRefinement _ _ = merror ".equalityRefinement: unexpected case."


leqUS :: IntDomain i => P.Program -> PState i UnSharing -> PState i UnSharing -> Bool
leqUS _ st1 st2 | trace ("LEQ:\n" ++ show st1 ++ "\n" ++ show st2) False = undefined
leqUS _ st1 st2 | not $ isSimilar st1 st2 = False
leqUS p st1 st2 
  | not $ all (`elem` paths1) paths2 = False
  | otherwise  = let b =
                            [checkValues paths2
                            ,checkDistinctness paths2
                            ,checkAlias refpaths2
                            ,checkMayAlias refpaths2 
                            ,propagateShare refpaths1
                            ,checkMayShare refpaths1
                            ,checkMaybeGraph refpaths1
                            ,propagateGraph refpaths1
                            ]
                in trace (show b) (and b)
  where
    paths1 = trace ("RPATHS1: " ++ show (rpaths st1)) rpaths st1
    paths2 = trace ("RPATHS2: " ++ show (rpaths st2)) rpaths st2
    {-paths1 = rpaths st1-}
    {-paths2 = rpaths st2-}

    refpaths1 = [ path | path <- paths1, RefVal _ <- [pval1 path]]
    refpaths2 = [ path | path <- paths2, RefVal _ <- [pval2 path]]

    -- TODO: shoold be a lookup table
    pval1 path = let v = rpathValue path st1 in trace ("valOf1: " ++ show path) v
    pval2 path = let v = rpathValue path st2 in trace ("valOf2: " ++ show path) v
    rval1 path = theAddress $ pval1 path
    rval2 path = theAddress $ pval2 path

    hp1 = heap st1
    hp2 = heap st2
    (ma1,ms1,mt1) = case annotations st1 of UnSharing ma ms mt -> (ma,ms,mt)
    (ma2,ms2,mt2) = case annotations st2 of UnSharing ma ms mt -> (ma,ms,mt)

    maxPath2 path = let mp = rmaxPrefix path refpaths2 in trace ("maxPath" ++ show (mp,path,refpaths2)) mp

    isNull Null = True
    isNull Unit = True
    isNull _    = False

    -- (a-d)
    checkValues ps | trace ("CV" ++ show ps) False = undefined
    checkValues pths = all checkPath pths
      where
        checkPath path   | trace ("cv: " ++ show path) False = undefined
        checkPath path   = checkValue (pval1 path) (pval2 path)
        checkValue v1 v2 = case (v1,v2) of
          (BoolVal a, BoolVal b) -> a `AD.leq` b
          (IntVal i, IntVal j)   -> i `AD.leq` j
          (Unit, IntVal i)       -> isTop i
          (Unit, BoolVal b)      -> isTop b
          (Unit, Unit)           -> True
          (Unit, Null)           -> True
          (Null, Null)           -> True
          (Null, RefVal q)       -> 
            case lookupH q hp2 of
              AbsVar _ -> True
              _        -> False
          (Unit, RefVal q)       -> 
            case lookupH q hp2 of
              AbsVar _ -> True
              _        -> False
          (RefVal q, RefVal r)   ->
            case (lookupH q hp1, lookupH r hp2) of
              (AbsVar cn, AbsVar cn')          -> P.isSuper p cn' cn
              (Instance cn _, AbsVar cn')      -> P.isSuper p cn' cn
              (Instance cn _, Instance cn' _)  -> cn == cn'
              _                                -> False
          _ -> False

    -- (e)
    checkDistinctness ps | trace ("CD" ++ show ps) False = undefined
    checkDistinctness pths = all distinctIn2 distinctPaths1
      where
        distinctIn2 (pathx,pathy) | trace ("cd: " ++ show (pathx,pathy)) False = undefined
        distinctIn2 (pathx,pathy) = cmp (pval2 pathx) (pval2 pathy)
        distinctPaths1 = do
          pathx <- pths
          pathy <- pths
          guard $ pathx /= pathy
          guard $ cmp (pval1 pathx) (pval1 pathy)
          return (pathx,pathy)
        cmp (RefVal q) (RefVal r) = q   /= r
        cmp _ _                   = True
    -- (f)
    checkAlias ps | trace ("CA" ++ show ps) False = undefined
    checkAlias pths = all maybeEuqalIn2 equalPaths1
      where
        maybeEuqalIn2 (pathx,pathy) | trace ("meq" ++ show (pathx,pathy)) False = undefined
        maybeEuqalIn2 (pathx,pathy) = 
          let r1 = rval2 pathx 
              r2 = rval2 pathy
          in  r1 == r2 || (r1:=?:r2 `S.member` ma2)
        equalPaths1 = do
          pathx <- pths
          pathy <- pths
          guard $ pathx /= pathy
          guard $ not (isNull (pval1 pathx) || isNull (pval1 pathy))
          guard $ rval1 pathx == rval1 pathy
          return (pathx,pathy)
    -- (g)
    checkMayAlias ps | trace ("CMA" ++ show ps) False = undefined
    checkMayAlias pths = all mayAliasIn2 mayAliasIn1
      where
        mayAliasIn2 (pathx,pathy) = rval2 pathx:=?:rval2 pathy `S.member` ma2
        mayAliasIn1 = do
          pathx <- pths
          pathy <- pths
          guard $ pathx /= pathy
          guard $ not (isNull (pval1 pathx) || isNull (pval1 pathy))
          guard $ rval1 pathx:=?: rval1 pathy `S.member` ma1
          return (pathx,pathy)
    -- (h)
    propagateShare ps | trace ("PRS" ++ show ps) False = undefined
    propagateShare pths = all maxPrefixIn2 mayEqualIn1
      where
        maxPrefixIn2 (pathx,pathy) = 
          if not $ pathx `elem` refpaths2 && pathy `elem` refpaths2
            then let valx = pval2 $ maxPath2 pathx
                     valy = pval2 $ maxPath2 pathy
                     (ref1,ref2) = ([ q | RefVal q <- [valx] ], [ r | RefVal r <- [valy]]) 
                 in if not (null ref1 || null ref2 || ref1 == ref2)  then head ref1:><:head ref2 `S.member` ms2 else True
            else True
        mayEqualIn1 = do
          pathx <- pths
          pathy <- pths
          let (r1,r2) = (rval1 pathx, rval1 pathy)
          guard $ pathx /= pathy
          guard $ r1 == r2 || (r1:=?:r2 `S.member` ma1)
          return (pathx,pathy)
    -- (i) 
    checkMayShare ps | trace ("CMS" ++ show ps) False = undefined
    checkMayShare pths = all maxShareIn2 mayShare1
      where
        maxShareIn2 (pathx,pathy) | trace ("cms: " ++ show (pathx,pathy)) False = undefined
        maxShareIn2 (pathx,pathy) = 
          let refx = rval2 (maxPath2 pathx)
              refy = rval2 (maxPath2 pathy)
          in if refx /= refy then refx:><:refy `S.member` ms2 else True
        mayShare1 = do
          pathx <- pths
          pathy <- pths
          let (r1,r2) = (rval1 pathx, rval1 pathy)
          guard $ r1:><:r2 `S.member` ms1
          return (pathx,pathy)
    -- (j)
    checkMaybeGraph ps | trace ("CMG" ++ show ps) False = undefined
    checkMaybeGraph pths = all maxGraphIn2 mayGraph1
      where
        maxGraphIn2 pathx = 
          NT (rval2 $ maxPath2 pathx) `S.member` mt2
        mayGraph1 = do
          pathx <- pths
          let r1 = rval1 pathx
          guard $ NT r1 `S.member` mt1
          return pathx
    -- (k)
    propagateGraph ps | trace ("PRG" ++ show ps) False = undefined
    propagateGraph pths = all maxGraphIn2 graphIn2
      where
        maxGraphIn2 (pathx,pathy,prefix) | trace ("prg: " ++ show (pathx,pathy,prefix)) False = undefined
        maxGraphIn2 (pathx,pathy,prefix) = 
          if not (pathx `elem` refpaths2 && pathy `elem` refpaths2)
             || rval2 pathx:=?:rval2 pathy `S.member` ma2
          then NT (rval2 $ maxPath2 prefix) `S.member` mt2
          else True
        graphIn2 = do
          pathx <- pths
          pathy <- pths
          let prefix = rcommonPrefix pathx pathy
          guard $ pathx /= pathy && isJust prefix
          guard $ maybe False (\lprefix -> isNotTreeShaped (rval1 lprefix) hp1) prefix
          return (pathx,pathy,fromJust prefix)  


joinUS :: (Monad m, IntDomain i) => PState i UnSharing -> PState i UnSharing -> JatM m (PState i UnSharing)
joinUS st1 st2 = do
  p <- getProgram
  st3 <- mergeStates p st1 st2 emptyUS
  let st3' = normalizeUS $ updateAnnotations st1 st2 st3
  if not (leqUS p st1 st3' && leqUS p st2 st3')
    then merror ".joinUS: not an abstraction."
    else return st3'
  {-return st3'-}


updateAnnotations :: IntDomain i => PState i UnSharing -> PState i UnSharing -> PState i UnSharing -> PState i UnSharing
updateAnnotations st1 st2 st3 = 
  let paths3     = rpaths st3
      refpaths3  = [ path | path <- paths3, RefVal _ <- [pval3 path]]
      pval3 path = rpathValue path st3
      rval3 path = theAddress $ pval3 path

      paths1     = rpaths st1
      refpaths1  = [ path | path <- paths1, RefVal _ <- [pval1 path]]
      pval1 path = rpathValue path st1
      rval1 path = theAddress $ pval1 path
        
      paths2     = rpaths st2
      refpaths2  = [ path | path <- paths2, RefVal _ <- [pval2 path]]
      pval2 path = rpathValue path st2
      rval2 path = theAddress $ pval2 path

      ma3 = updateAlias (st1,refpaths1,rval1) (refpaths3,rval3) `S.union` updateAlias (st2,refpaths2,rval2) (refpaths3,rval3)
      st3'@(PState hp3 frms3 _) = normalizeAlias ma3 st3

      paths3'     = rpaths st3'
      refpaths3'  = [ path | path <- paths3', RefVal _ <- [pval3' path]]
      pval3' path = rpathValue path st3'
      rval3' path = theAddress $ pval3' path

      ms3 = updateSharing (st1,refpaths1,rval1) (refpaths3',rval3') `S.union` updateSharing (st2,refpaths2,rval2) (refpaths3',rval3')
      mt3 = updateGraph (st1,refpaths1,rval1) (refpaths3',rval3',st3') `S.union` updateGraph (st2,refpaths2,rval2) (refpaths3',rval3',st3')
  in  PState hp3 frms3 (UnSharing ma3 ms3 mt3)
  where
    updateAlias (PState _ _ (UnSharing ma' _ _),refpaths',rval') (refpaths3,rval3) = 
      foldr addAlias S.empty differentPaths'
      where
        addAlias (pathx,pathy) ma | trace ("addAlias: " ++ show (pathx,pathy,ma)) False = undefined
        addAlias (pathx,pathy) ma = 
          if pathx `elem` refpaths3 && pathy `elem` refpaths3 && rval3 pathx /= rval3 pathy
            then rval3 pathx :=?: rval3 pathy `S.insert` ma
            else ma
        differentPaths' = do
          pathx <- refpaths'
          pathy <- refpaths'
          guard $ pathx /= pathy
          let (adrx,adry) = (rval' pathx, rval' pathy)
          guard $ adrx == adry || (adrx:=?:adry `S.member` ma')
          return (pathx,pathy)
    updateAlias _ _ = merror ".mergeAnnotations: exceptional state."

    normalizeAlias ma (PState hp frms (UnSharing _ ms mt)) = 
      normalizeUS $ PState (S.foldr abstraction hp ma) frms (UnSharing ma ms mt)
      where
        abstraction (q:=?:r) h = case (lookupH q hp, lookupH r hp) of
          (Instance _ _, Instance cn' _) -> updateH r (AbsVar cn') h
          _ -> h
    normalizeAlias _ _ = merror ".mergeAnnotations: exceptional state."

    updateSharing (PState _ _ (UnSharing ma' ms' _),refpaths',rval') (refpaths3,rval3) = 
      foldr addSharing S.empty differentPaths' `S.union` foldr propagateSharing S.empty sharingPaths'
      where
        addSharing (pathx,pathy) ms = 
          if not $ pathx `elem` refpaths3 && pathy `elem` refpaths3
            then let (mpx,mpy) = (maxRef3 pathx,maxRef3 pathy) in trace ("ADDSHARING:" ++ show (mpx,mpy)) $ mpx:><:mpy `S.insert` ms
            else ms
        propagateSharing (pathx,pathy) ms = maxRef3 pathx :><: maxRef3 pathy `S.insert` ms

        differentPaths' = do
          pathx <- refpaths'
          pathy <- refpaths'
          guard $ pathx /= pathy
          let (adrx,adry) = (rval' pathx, rval' pathy)
          guard $ adrx == adry || (adrx:=?:adry `S.member` ma')
          return (pathx,pathy)
        sharingPaths' = do
          pathx <- refpaths'
          pathy <- refpaths'
          guard $ pathx /= pathy
          let (adrx,adry) = (rval' pathx, rval' pathy)
          guard $ adrx:><:adry `S.member` ms'
          return (pathx,pathy)

        maxRef3 path = rval3 $ rmaxPrefix path refpaths3

    updateSharing _ _ = merror ".mergeAnnotations: exceptional state."

    updateGraph (PState hp' _ (UnSharing _ _ mt'),refpaths',rval') (refpaths3,rval3,st3') =
      foldr propagateGraph S.empty graphPaths `S.union` foldr addGraph S.empty cyclicPaths
      where
        propagateGraph pathx mt = NT (rval3 $ maxPath3 pathx) `S.insert` mt
        addGraph pth _ |trace ("addGraph: " ++ show (pth,pth `elem` refpaths3)) False = undefined
        addGraph pathx mt = 
          if pathx `elem` refpaths3 && isNotTreeShaped (rval3 pathx) (heap st3')
            then mt
            else trace ("NT: " ++ show pathx) $ NT (rval3 $ maxPath3 pathx) `S.insert` mt

        graphPaths = do
          pathx <- refpaths'
          guard $ NT (rval' pathx) `S.member` mt'
          return pathx
        cyclicPaths = do
          pathx <- refpaths'
          guard $ isNotTreeShaped (rval' pathx) hp'
          return pathx


        maxPath3 path = rmaxPrefix path refpaths3
    updateGraph _ _ = merror ".mergeAnnotations: exceptional state."

normalizeUS :: PState i UnSharing -> PState i UnSharing
normalizeUS (PState hp frms (UnSharing ma ms mt)) = PState hp' frms (UnSharing me' ms' mt')
   where
     refsF = [ r | RefVal r <- concatMap elemsF frms]
     hp'   = normalizeH refsF hp
     (me',ms',mt') = let refs = addresses hp' in
        ( S.filter (\(q:=?:r) -> q `elem` refs && r `elem` refs && q /= r && classH q == classH r) ma
        , S.filter (\(q:><:r) -> q `elem` refs && r `elem` refs && q /= r) ms
        , S.filter (\(NT q) -> q `elem` refs) mt
        )
     classH q = className $ lookupH q hp'
normalizeUS st = st

       
state2TRSUS :: (Monad m, IntDomain i) => Maybe Address -> PState i UnSharing -> Int -> JatM m (TRS.Term String String)
state2TRSUS m st@(PState hp _ (UnSharing _ ms mt)) = pState2TRS isSpecial isJoinable m st
  where
    isSpecial adr        = isCyclic adr hp || isNotTreeShaped  adr hp || NT adr `S.member` mt
    isJoinable adr1 adr2 = (adr1:><:adr2) `S.member` ms
state2TRSUS m st = pState2TRS undefined undefined m st
  




