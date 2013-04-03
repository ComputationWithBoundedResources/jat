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

data MayShare = Int :><: Int deriving Show
data MayAlias = Int :=?: Int deriving Show
data MayGraph = NT Int deriving (Eq,Ord,Show)

instance Eq MayShare where
  (q1:><:q2) == (r1:><:r2) = 
    (q1 == r1 && q2 == r2) || (q1 == r2 && q2 == r1) 

instance Ord MayShare where
  qs `compare` rs = compare (ord qs) (ord rs)
    where ord (q1:><:q2) = if q1 > q2 then (q1,q2) else (q2,q1)

instance Pretty MayShare where
  pretty (q1:><:q2) = text $ show q1 ++ "><" ++ show q2

instance Eq MayAlias where
  (q1:=?:q2) == (r1:=?:r2) = 
    (q1 == r1 && q2 == r2) ||
    (q1 == r2 && q2 == r1) 

instance Ord MayAlias where
  qs `compare` rs = compare (ord qs) (ord rs)
    where ord (q1:=?:q2) = if q1 > q2 then (q1,q2) else (q2,q1)

instance Pretty MayAlias where
  pretty (q1:=?:q2) = text $ show q1 ++ "=?" ++ show q2

instance Pretty MayGraph where
  pretty (NT q) = text $ '&': show q

data UnSharing = UnSharing (S.Set MayAlias) (S.Set MayShare) (S.Set MayGraph) deriving (Eq,Ord,Show)

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
  pretty (UnSharing ms ma mg) =
    (hsep . map pretty $ S.elems ms)
    <$> (hsep . map pretty $ S.elems ma)
    <$> (hsep . map pretty $ S.elems mg)

instance MemoryModel UnSharing where
  new       = new'
  getField  = getField'
  putField  = putField'

  invoke    = undefined
  equals    = equals'
  nequals   = nequals'

  initMem   = undefined

  leq       = undefined
  join      = undefined

  state2TRS = undefined

new' :: (Monad m, IntDomain i) => P.Program -> PState i UnSharing -> P.ClassId -> JatM m (PStep(PState i UnSharing))
new' p (PState hp (Frame loc stk cn mn pc :frms) ann) newcn = 
  let obt     = mkInstance p newcn
      (a,hp') = insertHA obt hp
      stk'    = RefVal a :stk
  in
  return $ topEvaluation (PState hp' (Frame loc stk' cn  mn (pc+1) :frms) ann)
new' _ _ _ = error "Jat.PState.MemoryModel.UnSharing.new: unexpected case."


getField' :: (Monad m, IntDomain i) => P.Program -> PState i UnSharing -> P.ClassId -> P.FieldId -> JatM m (PStep(PState i UnSharing))
getField' _ st cn fn = case opstk $ frame st of
  Null :_        -> return $ topEvaluation (EState NullPointerException)
  RefVal adr : _ -> tryInstanceRefinement st adr |>> return (mkGetField st adr cn fn)
  _              -> error "Jat.MemoryModel.UnSharing.getField: unexpected case."

mkGetField :: (MemoryModel a, IntDomain i) => PState i a -> Address -> P.ClassId -> P.FieldId -> PStep (PState i a)
mkGetField (PState hp (Frame loc stk cn mn pc :frms) ann) adr cn1 fn1 = 
  case lookupH adr hp of
    AbsVar _      -> error "Jat.MemoryModel.UnSharing.mkGetField: unexpected case"
    Instance _ ft -> let stk' = lookupFT cn1 fn1 ft : tail stk
                    in topEvaluation (PState hp (Frame loc stk' cn  mn (pc+1) :frms) ann)
mkGetField _ _ _ _ = error "Jat.MemoryModel.UnSharing.mkGetField: unexpected case"

putField' ::(Monad m, IntDomain i) => P.Program -> PState i UnSharing -> P.ClassId -> P.FieldId -> JatM m (PStep(PState i UnSharing))
putField' _ st cn fn = case opstk $ frame st of
  _ : Null : _        -> return $ topEvaluation (EState NullPointerException)
  v : RefVal adr : _ -> tryInstanceRefinement st adr |> tryEqualityRefinement st adr |>> mkPutField st adr cn fn v
  _              -> error "Jat.MemoryModel.UnSharing.getField: unexpected case."

mkPutField :: (Monad m, IntDomain i) => PState i UnSharing -> Address -> 
             P.ClassId -> P.FieldId -> AbstrValue i -> JatM m (PStep (PState i UnSharing))
mkPutField st@(PState hp (Frame loc (_:_:stk) cn mn pc :frms) us) adr cn1 fn1 v = 
  case lookupH adr hp of
    AbsVar _         -> error "Jat.PState.MemoryModel.Sharing.putField: unexpected case"
    Instance cn2 ft ->  return $ topEvaluation  (mkPut cn2 ft)
  where
    mkPut dn ft = PState (updateH adr (mkObt dn ft) hp) (Frame loc stk cn mn (pc+1):frms) (updateAnnot us)
    mkObt cn ft = Instance cn (updateFT cn1 fn1 v ft)
    updateAnnot us@(UnSharing me ms mt) = case v of
      RefVal o0 -> UnSharing me (ms `S.union` newShares) (mt `S.union` newGraphs1 `S.union` newGraphs2)
      _ -> us
      where
        o1 = let RefVal o1 = v in o1
        o0 = adr 

        newShares = [ p:><:q | p <- annotatedWith st o1, q <- reaches st o0, p/=q ]
        newGraphs1 = [ NT p | p <- reachedBy st o1, q1 <- reaches st p, q2 <- reaches st o0, q1 == q2,  anyNonCommonPrefix]
          where anyNonCommonPrefix = undefined
        newGraphs2 = if hasCommonSuccessor o0 hp ||  any (\q -> NT q `S.member` mt) (reachable o0 hp)
                        then [NT p | p <- annotatedWith st o1]
                        else S.empty 

equals' :: (Monad m, IntDomain i) => P.Program -> PState i UnSharing -> JatM m (PStep(PState i UnSharing))
equals' _ st@(PState hp (Frame loc (v1:v2:stk) cn mn pc :frms) us@(UnSharing ma _ _)) =
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
    equalsx _ _ = error "equals: unexpected case"
    mkBool b = return . topEvaluation $ PState hp (Frame loc stk' cn mn (pc+1):frms) us
      where stk' = BoolVal (AD.constant b) : stk
equals' _ _ = error "Jat.PState.MemoryModel.UnSharing.equals: unexpected case."

nequals' _ st@(PState hp (Frame loc (v1:v2:stk) cn mn pc :frms) us@(UnSharing ma _ _)) =
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
    nequalsx _ _ = error "nequals: unexpected case"
    mkBool b = return . topEvaluation $ PState hp (Frame loc stk' cn mn (pc+1):frms) us
      where stk' = BoolVal (AD.constant b) : stk
nequals' _ _ = error "Jat.PState.MemoryModel.UnSharing.equals: unexpected case."

mkAbsInstance :: (Monad m, IntDomain i) => Heap i -> Address -> P.ClassId -> JatM m  (Heap i, Object i)
mkAbsInstance hp adr cn = do
  p <- getProgram
  (hp1,ifds) <- initfds $ P.hasFields p cn
  let obt = mkObt cn ifds
      hp2 = updateH adr obt hp1
  return (hp2,obt)
  where 
    initfds = initfds' (return (hp,[]))
    initfds' m [] = m
    initfds' m ((ln1,cn1,tp1):fds) = do
      (hp1,ifds) <- m
      (hp2,v) <- defaultAbstrValue hp1 tp1
      initfds' (return (hp2, (cn1,ln1,v):ifds)) fds

    mkObt cn1 fds = Instance cn1 (mkFt fds)
    mkFt = foldl (flip $ curry3 updateFT) emptyFT
    curry3 f (a,b,c) = f a b c

    defaultAbstrValue :: (IntDomain i) => Monad m => Heap i -> P.Type -> JatM m (Heap i, AbstrValue i)
    defaultAbstrValue hp1 (P.BoolType)   = do {v <- AD.top; return (hp1,BoolVal v)}
    defaultAbstrValue hp1 (P.IntType)    = do {v <- AD.top; return (hp1,IntVal v)}
    defaultAbstrValue hp1 (P.RefType cn1) = return (hp2, RefVal r)
      where (r, hp2) = insertHA (AbsVar cn1) hp1
    defaultAbstrValue _ _              = error "Jat.PState.MemoryModel.UnSharing.mkAbsInstance: unexpected type."
    
--initMem' ::(Monad m, IntDomain i) => P.Program -> P.ClassId -> P.MethodId -> JatM m (PState i UnSharing)
--initMem' p cn mn = do
  --let m = P.theMethod p cn mn
  --heap1 = addAbsInstance 0 cn emptyH
  --this <- abstractInstance
  --(heap,params) <- foldM defaultAbstrValue (P.methodParams m)
  --let loc = initL params $ P.maxLoc m
  --return $ PState emptyH [Frame loc [] cn mn 0]
  --where
    --defaultAbstrValue acc [] = acc
    --defaultAbstrValue (hp,params) (t:tys) = case t of
      --P.BoolType -> AD.top >>= \b -> return $ (hp, params++[BoolVal b])
      --P.IntTyp   -> AD.top >>= \i -> return $ (hp, params++[IntVal i])
      --P.NullType -> return $ (hp, params++[Null])
      --P.Void     -> return $ (hp, params++[Unit])
      --P.RefType cn -> return $ (hp', params++[RefVal r])
        --where (r, hp') = insertH2 (AbsVar cn) hp

--addAbsInstance :: (IntDomain i) => Address -> P.ClassId -> Heap i a -> JatM m (Heap i a)
--addAbsInstance p heap a cn = do
  --(heap',ifds) <- initfds' fds
  --let obt = mkObt cn ifds
      --heap'' = updateH a obt heap'
  --return (heap'')
  --where 
    --fds     = P.hasFields p cn
    --initfds' fds = initfds (return (heap,[])) fds
    --initfds m [] = m
    --initfds m ((ln,cn,tp):fds) = do
      --(h,ifds) <- m
      --(h',v) <- defaultAbstrValue h tp
      --initfds (return (h', (cn,ln,v):ifds)) fds

    --mkObt cn fds = Instance cn (mkFt fds)
    --mkFt = foldl (flip $ curry3 updateFT) emptyFT
    --curry3 f (a,b,c) = f a b c

    --defaultAbstrValue :: (IntDomain i) => Heap i-> P.Type -> Jat (Heap i, AbstrValue i)
    --defaultAbstrValue h (P.BoolType)   = do {v <- top; return (h,BoolVal v)}
    --defaultAbstrValue h (P.IntType)    = do {v <- top; return (h,IntVal v)}
    --defaultAbstrValue h (P.RefType cn) = return (h', RefVal r)
      --where (r, h') = insertHA (AbsVar cn) h
    --defaultAbstrValue _ _              = error "Jat.PState.Opsem.instanceRefinement: unexpected type"




  --let m   = P.theMethod p cn mn
  --params <- mapM defaultAbstrValue $ P.methodParams m 
  --let loc = initL params $ P.maxLoc m
  --return $ PState emptyH [Frame loc [] cn mn 0]
  --where 
    --defaultAbstrValue P.BoolType = BoolVal `liftM` AD.top
    --defaultAbstrValue P.IntType  = IntVal `liftM` AD.top
    --defaultAbstrValue P.NullType = return Null
    --defaultAbstrValue P.Void     = return Unit
    --defaultAbstrValue _          = error "Jat.PState.MemorModel.Primitive: not supported"







annotatedWith :: PState i UnSharing -> Address -> Set Address
annotatedWith st adr = S.fromList (adr `mayAliasWith` ann) `S.union` S.fromList (adr `mayShareWith` ann)
  where ann = annotations st

reaches :: PState i UnSharing -> Address -> Set Address
reaches st adr = S.unions $ S.fromList reachables : map (annotatedWith st) reachables
  where reachables = reachable adr (heap st)

reachedBy :: PState i UnSharing -> Address -> Set Address
reachedBy st adr1 = S.fromList $ filter (\adr2 -> adr1 `S.member` reaches st adr2) (addresses $ heap st) 


tryInstanceRefinement :: (Monad m, IntDomain i) => PState i UnSharing -> Address -> JatM m (Maybe (PStep(PState i UnSharing)))
tryInstanceRefinement st@(PState hp _ _) q = 
    tryEqualityRefinementWithInstance st q |> case lookupH q hp of
      AbsVar _     -> getProgram >>= \p -> Just `liftM` instanceRefinement p st q
      Instance _ _ -> return Nothing 
tryInstanceRefinement _ _ = error "Jat.MemoryModel.UnSharing.tryInstanceRefinement: exceptional case."



-- o1-><-o2 : and o1 is Unknown
-- o1->1 o *<-o2
-- if o1 is refined
  -- kids could equal to o2
  -- if o2 is Instance then original annot can be removed
  -- if o2 is Abstract then annot have to be kept due to "symmetry" of -><-
instanceRefinement :: (Monad m, IntDomain i) => P.Program -> PState i UnSharing -> Address -> JatM m (PStep(PState i UnSharing))
instanceRefinement p st@(PState hp frms ann) adr = do
  instances <- instancesM
  nullref   <- nullM
  return . topRefinement $ nullref:instances
  where
    cns  = P.subClassesOf p . className $ lookupH adr hp
    obtM = mapM (mkAbsInstance hp adr) cns

    instancesM = map mkInstance `liftM` obtM
      where mkInstance (hp1,obt1) = let hp2 = updateH adr obt1 hp1 in PState hp2 frms (updateSharing hp2 adr obt1 ann)
    nullM      = return $ substitute (RefVal adr) Null st
    

    updateSharing :: Heap i -> Address -> Object i -> UnSharing -> UnSharing
    updateSharing hp adr obj ann@(UnSharing ma ms mt) =
      let ma' = ma `S.union` S.fromList newAliases1 `S.union` S.fromList newAliases2
          ms' = S.filter thefilter ms `S.union` S.fromList newSharing1 `S.union` S.fromList newSharing2
          mt' = mt `S.union` S.fromList newGraphs
      in UnSharing ma' ms' mt'
      where
        sharesWith = adr `mayShareWith` ann
        obtrefs    = referencesO obj

        thefilter (ref1:><:ref2) = not $ (ref1 == adr || ref2 == adr) && isInstanceH ref1 && isInstanceH ref2 
        newAliases1 = [ new :=?: old | new <- obtrefs, old <- sharesWith]
        newSharing1 = [ new :><: old | new <- obtrefs, old <- sharesWith]
        
        (newAliases2, newSharing2, newGraphs) =
          if NT adr `S.member` mt
            then
            ( [ new1:=?:new2 | new1 <- adr:obtrefs, new2 <- obtrefs, new1 /= new2, let {cn1 = classNameH new1; cn2 = classNameH new2} in cn1 `isSuper` cn2 || cn2 `isSuper` cn1]
            , [ new1:><:new2 | new1 <- adr:obtrefs, new2 <- obtrefs, new1 /= new2]
            , [ NT ref | ref <- obtrefs])
            else ([],[],[])
        classNameH cn  = className $ lookupH cn hp
        isSuper        = P.isSuper p
        isInstanceH ref = isInstance $ lookupH ref hp



tryEqualityRefinement :: (Monad m, IntDomain i) => PState i UnSharing -> Address -> JatM m  (Maybe (PStep (PState i UnSharing)))
tryEqualityRefinement st r =
  case anyEqualityRefinementWithInstance st r of
    Just r' -> return . Just $ equalityRefinement st r'
    Nothing -> return Nothing

anyEqualityRefinement :: (IntDomain i) => PState i UnSharing -> Address -> Maybe MayAlias
anyEqualityRefinement (PState hp _ ann) q = 
  case q `mayAliasWith` ann of
   (r:_) -> Just (q:=?:r)
   []    -> Nothing
anyEqualityRefinement _ _ = error "Jat.MemoryModel.UnSharing.anyEqualityRefinement: exceptional case."
                                                                                                                 --
-- like tryEqualityRefinement, but considers only the case if the aliased references is an instance
tryEqualityRefinementWithInstance :: (Monad m, IntDomain i) => PState i UnSharing -> Address -> JatM m  (Maybe (PStep (PState i UnSharing)))
tryEqualityRefinementWithInstance st r =
  case anyEqualityRefinementWithInstance st r of
    Just r' -> return . Just $ equalityRefinement st r'
    Nothing -> return Nothing

anyEqualityRefinementWithInstance :: (IntDomain i) => PState i UnSharing -> Address -> Maybe MayAlias
anyEqualityRefinementWithInstance (PState hp _ ann) q = anyq aliases
  where
    aliases = q `mayAliasWith` ann
    anyq (r:rs)     = 
      case lookupH r hp of 
        Instance _ _ -> Just (q:=?:r)
        _            -> anyq rs
    anyq [] = Nothing
anyEqualityRefinementWithInstance _ _ = error "Jat.MemoryModel.UnSharing.anyEqualityRefinementWithInstance: exceptional case."

equalityRefinement :: (IntDomain i) => PState i UnSharing -> MayAlias -> PStep (PState i UnSharing)
equalityRefinement st@(PState hp frms (UnSharing ma ms mt)) (ref1:=?:ref2) = 
  case (lookupH ref1 hp, lookupH ref2 hp) of
    (AbsVar _, _) -> topRefinement [mkEqual ref1 ref2, mkNequal]
    (_, AbsVar _) -> topRefinement [mkEqual ref2 ref1, mkNequal]
    _ -> error "Jat.PState.MemoryModel.UnSharing.equalityRefinement: unexpected case"
  where
    me' = (/= (ref1:=?:ref2)) `S.filter` ma
    mkEqual r1 r2 =  
      let PState hp1 fs1 (UnSharing _ ms1 mt1) = substitute (RefVal r1) (RefVal r2) st
      in  PState hp1 fs1 (UnSharing me' ms1 mt1)
    mkNequal = PState hp frms (UnSharing me' ms mt)
equalityRefinement _ _ = error "Jat.MemoryModel.UnSharing.equalityRefinement: unexpected case."


data Root = RStk Int Int | RLoc Int Int deriving (Eq,Show)
data Path = Path Root  [(P.ClassId, P.FieldId)]  | Empty deriving (Eq,Show)



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

  













