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

import qualified Data.Set as S

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
  equals    = undefined
  nequals   = undefined

  initMem   = undefined

  leq       = undefined
  join      = undefined

  state2TRS = undefined


mkAbsInstance :: (Monad m, IntDomain i) => Heap i a -> Address -> P.ClassId -> JatM m  (Heap i a, Object i)
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

    defaultAbstrValue :: (IntDomain i) => Monad m => Heap i a -> P.Type -> JatM m (Heap i a, AbstrValue i)
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


new' :: (Monad m, IntDomain i) => P.Program -> PState i UnSharing -> P.ClassId -> JatM m (PStep(PState i UnSharing))
new' p (PState hp (Frame loc stk cn mn pc :frms)) newcn = do 
  let obt     = mkInstance p newcn
      (a,hp') = insertHA obt hp
      stk'    = RefVal a :stk
  return $ topEvaluation (PState hp' (Frame loc stk' cn  mn (pc+1) :frms))
new' _ _ _ = error "Jat.PState.MemoryModel.UnSharing.new: unexpected case."

mkInstance :: IntDomain i => P.Program -> P.ClassId -> Object i
mkInstance p cn = Instance cn (mkFt . initfds $ fds)
  where
    fds     = P.hasFields p cn
    initfds = map (\(lfn,lcn,ltp) -> (lcn,lfn,defaultValue ltp))
    mkFt    = foldl (flip $ curry3 updateFT) emptyFT
    curry3 f (a,b,c) = f a b c


getField' :: (Monad m, IntDomain i) => P.Program -> PState i UnSharing -> P.ClassId -> P.FieldId -> JatM m (PStep(PState i UnSharing))
getField' _ st cn fn = case opstk $ frame st of
  Null :_        -> return $ topEvaluation (EState NullPointerException)
  RefVal adr : _ -> tryInstanceRefinement st adr |>> (return $ mkGetField st adr cn fn)
  _              -> error "Jat.MemoryModel.UnSharing.getField: unexpected case."

mkGetField :: (MemoryModel a, IntDomain i) => PState i a -> Address -> P.ClassId -> P.FieldId -> PStep (PState i a)
mkGetField (PState hp (Frame loc stk cn mn pc :frms)) adr cn1 fn1 = 
  case lookupH adr hp of
    AbsVar _      -> error "Jat.MemoryModel.UnSharing.mkGetField: unexpected case"
    Instance _ ft -> let stk' = lookupFT cn1 fn1 ft :stk
                    in topEvaluation (PState hp (Frame loc stk' cn  mn (pc+1) :frms))
mkGetField _ _ _ _ = error "Jat.MemoryModel.UnSharing.mkGetField: unexpected case"

putField' ::(Monad m, IntDomain i) => P.Program -> PState i UnSharing -> P.ClassId -> P.FieldId -> JatM m (PStep(PState i UnSharing))
putField' _ st cn fn = case opstk $ frame st of
  Null :_        -> return $ topEvaluation (EState NullPointerException)
  RefVal adr : _ -> tryInstanceRefinement st adr |> tryEqualityRefinement st adr |>> mkPutField st adr cn fn
  _              -> error "Jat.MemoryModel.UnSharing.getField: unexpected case."

mkPutField = undefined 



tryInstanceRefinement :: (Monad m, IntDomain i) => PState i UnSharing -> Address -> JatM m (Maybe (PStep(PState i UnSharing)))
tryInstanceRefinement st@(PState hp _) q = 
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
instanceRefinement p st@(PState hp frms) adr = do
  instances <- instancesM
  nullref   <- nullM
  return . topRefinement $ nullref:instances
  where
    cns  = P.subClassesOf p . className $ lookupH adr hp
    obtM = mapM (mkAbsInstance hp adr) cns

    instancesM = map mkInstance `liftM` obtM
      where mkInstance (hp1,obt1) = let hp2 = updateH adr obt1 hp1 in PState (mapAnnotations (updateSharing hp1 adr obt1) hp1) frms
    nullM      = return $ substitute (RefVal adr) Null st
    

    updateSharing :: Heap i UnSharing -> Address -> Object i -> UnSharing -> UnSharing
    updateSharing hp adr obj = case annotations hp of
        UnSharing ma ms mt -> 
          let ma' = ma `S.union` S.fromList newAliases1 `S.union` S.fromList newAliases2
              ms' = S.filter thefilter ms `S.union` S.fromList newSharing1 `S.union` S.fromList newSharing2
              mt' = mt `S.union` S.fromList newGraphs
          in const $ UnSharing ma' ms' mt'
          where
            sharesWith = adr `mayShareWith` annotations hp
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
anyEqualityRefinement (PState hp _) q = 
  case q `mayAliasWith` annotations hp of
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
anyEqualityRefinementWithInstance (PState hp _) q = anyq aliases
  where
    aliases = q `mayAliasWith` annotations hp
    anyq (r:rs)     = 
      case lookupH r hp of 
        Instance _ _ -> Just (q:=?:r)
        _            -> anyq rs
    anyq [] = Nothing
anyEqualityRefinementWithInstance _ _ = error "Jat.MemoryModel.UnSharing.anyEqualityRefinementWithInstance: exceptional case."

equalityRefinement = undefined

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

  













