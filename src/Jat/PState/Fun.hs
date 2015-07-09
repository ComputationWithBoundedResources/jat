-- | This module provides common functionality for abstract states.
module Jat.PState.Fun
  (
    mkInstance
  , mkAbsInstance
  , mergeStates
  , Correlation (..)
  , mergeStates'
  , mkGetField
  , mkPutField
  , pState2TRS

  , instruction
  , isTerminal
  , isSimilar
  {-, isBackJump-}
  , isTarget
  , maybePutField

  , mapAnnotations
  , mapValues
  , mapValuesFS
  , substitute

  , rpaths
  , rpathValue  
  , rcommonPrefix
  , rmaxPrefix

  , valueV
  , typeV
  , reachableV
  , programLocation
  , tyOf
  , refKindOf
  )
where

import qualified Jat.Constraints as PA
import Jat.PState.AbstrValue
import Jat.PState.Data
import Jat.PState.Frame
import Jat.PState.Object
import Jat.PState.IntDomain.Data
import Jat.PState.MemoryModel.Data
import Jat.PState.Heap
import Jat.PState.Step
import Jat.PState.AbstrDomain as AD
import Jat.JatM
import qualified Jinja.Program as P
import Jat.Utils.Pretty

import Data.Char (toLower)
import qualified Data.Array as A
import Data.List (inits)
import qualified Data.Map as M
import Data.Maybe (fromJust)
import Control.Monad.State

--import Debug.Trace

-- | Returns a (concrete) 'Object' of the given class.
mkInstance :: IntDomain i => P.Program -> P.ClassId -> Object i
mkInstance p cn = Instance cn (mkFt . initfds $ fds)
  where
    fds     = P.hasFields p cn
    initfds = map (\(lfn,lcn,ltp) -> (lcn,lfn,defaultValue ltp))
    mkFt    = foldl (flip $ curry3 updateFT) emptyFT
    curry3 f (a,b,c) = f a b c

-- | Constructs an instance with its field set to be abstract values.
-- Returns the heap (including) the new instance and the instance itself.
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
    defaultAbstrValue _ _              = error "Jat.PState.Fun.mkAbsInstance: unexpected type."

data Correlation = C Address Address deriving (Show,Eq,Ord)

correlation :: Address -> Address -> Correlation
correlation = C

data Corre i = Corr {unCorr :: M.Map Correlation Address, unHeap:: Heap i}

mergeStates :: (Monad m, MemoryModel a, IntDomain i) => P.Program -> PState i a -> PState i a -> a -> JatM m (PState i a)
mergeStates p s1 s2 a = fst `liftM` mergeStates' p s1 s2 a

-- | Given two states, builds a new states with maximal common paths and maximal common aliasing.
mergeStates' :: (Monad m, MemoryModel a, IntDomain i) => P.Program -> PState i a -> PState i a -> a -> JatM m (PState i a, M.Map Correlation Address)
mergeStates' _ st1 st2 _ | not (isSimilar st1 st2) = error "Jat.PState.Fun.mergeStates: non-similar states."
mergeStates' p (PState hp1 frms1 _) (PState hp2 frms2 _) ann = do
  (st,frms3) <- wideningFs Corr{unCorr=M.empty, unHeap=emptyH} frms1 frms2
  return (PState (unHeap st) frms3 ann, unCorr st)
    where
      wideningF st (Frame loc1 stk1 cn mn pc) (Frame loc2 stk2 _ _ _) = do
        (st1,loc3) <- joinValM st loc1 loc2
        (st2,stk3) <- joinValM st1 stk1 stk2
        return (st2,Frame loc3 stk3 cn mn pc)

      wideningFs st [] []           = return (st,[])
      wideningFs st (f1:fs1) (f2:fs2) = do
        (st1,f3)  <- wideningF st f1 f2
        (st2,fs3) <- wideningFs st1 fs1 fs2
        return (st2,f3:fs3)
      wideningFs _ _ _              = error "unexpected case"

      --joinVal _ i j | trace (show (pretty i<> pretty j)) False = undefined
      joinVal st (IntVal i) (IntVal j)   = do
        k <- i `AD.lub` j
        return (st, IntVal k)
      joinVal st (BoolVal a) (BoolVal b) = do
        c <- a `AD.lub` b
        return (st, BoolVal c)
      joinVal st (RefVal q) (RefVal r) = 
        case correlation q r `M.lookup` unCorr st of
          Just a -> return (st,RefVal a)
          Nothing -> do
            let (a,hp') = insertHA undefined (unHeap st)
                cors = M.insert (correlation q r) a (unCorr st)
                st'  = st{unCorr=cors,unHeap = hp'}

            st'' <- joinObject st' a (lookupH q hp1) (lookupH r hp2)
            return (st'',RefVal a)
      joinVal st Null Null        = return (st,Null)
      joinVal st Unit Null        = return (st,Null)

      joinVal st Null (IntVal _)  = (,) st `liftM` IntVal `liftM` top
      joinVal st Null (BoolVal _) = (,) st `liftM` BoolVal `liftM` top
      joinVal st Null (RefVal r)  = do
        let (a,heapt) = insertHA (AbsVar . className $ lookupH r hp2) (unHeap st)
        return (st{unHeap=heapt},RefVal a)
      joinVal st (RefVal r) Null  = do
        let (a,heap') = insertHA (AbsVar . className $ lookupH r hp1) (unHeap st) 
        return (st{unHeap=heap'},RefVal a)
      
      joinVal st Null Unit        = return (st, Null)
      joinVal st v Null           = joinVal st Null v
      joinVal st Unit (IntVal _)  = (,) st `liftM` IntVal `liftM` top
      joinVal st Unit (BoolVal _) = (,) st `liftM` BoolVal `liftM` top
      joinVal st Unit (RefVal r)  = joinVal st Null (RefVal r)
      joinVal st (RefVal r) Unit  = joinVal st (RefVal r) Null
      joinVal st Unit Unit        = return (st, Null)
      joinVal st v Unit           = joinVal st Unit v
      joinVal _ _ _ = error "unexpected case."

      joinObject st a (Instance cn ft) (Instance cn' ft') | cn == cn' = do
        (st',vs) <- joinValM st (M.elems ft) (M.elems ft')
        let ft'' = M.fromList $ zip (M.keys ft) vs
            hp'  = updateH a (Instance cn ft'') (unHeap st')
        return st'{unHeap=hp'}
      joinObject st a (Instance cn _) (Instance cn' _) = addAbsVar st a cn cn'
      joinObject st a (AbsVar cn) (Instance cn' _)     = addAbsVar st a cn cn'
      joinObject st a (Instance cn _) (AbsVar cn')     = addAbsVar st a cn cn'
      joinObject st a (AbsVar cn) (AbsVar cn')         = addAbsVar st a cn cn'

      addAbsVar st a cn cn' = do
        let dn = P.theLeastCommonSupClass p cn cn'
            hp'= updateH a (AbsVar dn) (unHeap st)
        return st{unHeap=hp'}
        
      --joinValMS st [] []           = return (st,[])
      --joinValMS st (l:ls) (l':ls') = do
        --(st',l'') <- joinValM st l l'
        --(d,e) <- joinValMS st' ls ls'
        --return (d,l'':e)
      --joinValMS _ _ _ = error "Jat.PState.Fun.mergeStates: unexpected case."

      joinValM st [] []           = return (st,[])
      joinValM st (v:vs) (v':vs') = do
        (st',v'') <- joinVal st v v'
        (d,e) <- joinValM st' vs vs'
        return (d, v'':e)
      joinValM _ _ _ = error "Jat.PState.Funl.mergeStates: unexpected case: illegal fieldtable"
mergeStates' _ _ _ _ = error "Jat.PState.Fun.mergeStates: unexpected case."


-- | Performs Getfield, assuming it is valid to perform. 
mkGetField :: (MemoryModel a, IntDomain i) => PState i a -> P.ClassId -> P.FieldId -> PStep (PState i a)
mkGetField (PState _ (Frame _ (Null:_) _ _ _ :_) _) _ _ =  topEvaluation $ EState NullPointerException
mkGetField (PState hp (Frame loc (RefVal adr:stk) cn1 mn pc :frms) us) cn2 fn = 
  case lookupH adr hp of
    AbsVar _      -> error "Jat.PState.Fun.mkGetField: unexpected case."
    Instance _ ft -> let stk' = lookupFT cn2 fn ft :stk
                    in topEvaluation (PState hp (Frame loc stk' cn1  mn (pc+1) :frms) us)
mkGetField _ _ _ = error "Jat.PState.Fun.mkGetField: unexpected case"

-- | Performs Putfield, assuming it is valid to perform.
mkPutField :: (Monad m, IntDomain i, MemoryModel a) => a -> PState i a -> P.ClassId -> P.FieldId -> JatM m (PStep (PState i a))
mkPutField us2 st@(PState hp (Frame loc fstk fcn mn pc :frms) us1) cn fn = 
  return $ case opstk $ frame st of
  _            : Null      : _ ->  topEvaluation $ EState NullPointerException
  v@(RefVal _) : RefVal o1 : _ ->  topEvaluation $ mkPut v o1 us2
  v            : RefVal o1 : _ ->  topEvaluation $ mkPut v o1 us1
  _ -> error "Jat.PState.Fun.putField: unexpected case."
  where
    mkPut v o1 uso = case lookupH o1 hp of
      AbsVar _         -> error "Jat.PState.Fun.mkPutField: unexpected case."
      Instance cno fto -> 
        let (_:_:stk) = fstk
            obt = Instance cno (updateFT cn fn v fto)
            hp' = updateH o1 obt hp
        in  PState hp' (Frame loc stk fcn mn (pc+1):frms) uso
mkPutField _ _ _ _ = error "Jat.PState.Fun.mkPutField: unexpected case."


-- | Returns the cTRS representation of a state, given functions for checking cyclicity and joinability.
pState2TRS :: (Monad m, IntDomain i, Pretty a) => 
  (Address -> Bool)
  -> (Address -> Address -> Bool)
  -> Maybe Address
  -> Side
  -> PState i a -> Int -> JatM m PA.PATerm
pState2TRS isSpecial maybeReaches m side (PState hp frms _) k = do
  key <- nextVarIdx
  return $ PA.ufun ('f':show k)  $ evalState (mapM tval (concatMap elemsF frms)) key
  {-return $ PA.ufun ('f':show k)  $ evalState (return []) [key..]-}
  where
    fresh :: State Int Int
    fresh = modify succ >> get 

    nullterm = PA.ufun "null" []
    var cn   = PA.uvar (map toLower cn)
    
    tval :: AbstrDomain i b => AbstrValue i -> State Int PA.PATerm
    tval Null        = return nullterm
    tval Unit        = return nullterm
    tval (RefVal r)  = taddr r
    tval (BoolVal b) = return $ atom b
    tval (IntVal i)  = return $ atom i

        
    {-taddr r | trace (">> taddr" ++ show r ++ show st) False = undefined-}
    taddr r = case m of
      Just q  -> taddrStar q r
      Nothing -> taddr' r

    taddr' r | isSpecial r = do
      key <- fresh
      let cn = className $ lookupH r hp
      return $ var ('c':show side ++ showcn cn) key
    taddr' r =
      case lookupH r hp of
        AbsVar cn      -> return $ var (showcn cn) r
        Instance cn ft -> PA.ufun (showcn cn) `liftM` mapM tval (elemsFT ft)

    
    {-taddrStar q r | trace (">> taddrStar" ++ show (q,r,maybeReaches r q, st)) False = undefined-}
    taddrStar q r
      | maybeReaches r q = do
        key <- fresh
        let cn = className $ lookupH r hp
        return $ var ('x':show side ++ showcn cn) key
      | otherwise = taddr' r
    showcn = show . pretty

pState2TRS _ _ _ _ (EState  ex) _ = return $ PA.ufun (show ex) []
  


-- | Returns current instruction.
instruction :: P.Program -> PState i a -> P.Instruction
instruction p (PState _ (Frame _ _ cn mn pc :_) _) = P.instruction p cn mn pc

-- | Checks if current state is a terminal state, ie. a state with an empty
-- frame list or an exceptional state.
isTerminal :: PState i a -> Bool
isTerminal (PState _ frms _) = null frms
isTerminal (EState _)        = True

-- | Checks if two states are similar.
-- Two states are similar if the class name, field name and program counter of
-- its frames correspond.
isSimilar :: PState i a -> PState i a -> Bool
isSimilar (PState _ frms1 _) (PState _ frms2 _) = isSimilarFS frms1 frms2
  where
    isSimilarFS (f1:fs1) (f2:fs2) = isSimilarF f1 f2 && isSimilarFS fs1 fs2
    isSimilarFS [][]              = True
    isSimilarFS _ _               = False
    isSimilarF (Frame loc1 stk1 cn1 mn1 pc1) (Frame loc2 stk2 cn2 mn2 pc2) = 
      cn1 == cn2 && mn1 == mn2 && pc1 == pc2 
      && length loc1 == length loc2 && length stk1 == length stk2
isSimilar _ _ = False

{-isBackJump :: Monad m => PState i a -> JatM m Bool -}
{-isBackJump (PState _ (Frame _ _ cn mn pc:_) _) = getProgram >>= \p -> return $ P.isBackJump p cn mn pc-}
{-isBackJump _                                   = return False-}

-- | Checks if current state is target for a backjump.
isTarget :: Monad m => PState i a -> JatM m Bool 
isTarget (PState _ (Frame _ _ cn mn pc:_) _) = do
  p <- getProgram
  return $ pc `elem` [ pc'+i | (pc', P.Goto i) <- A.assocs $ P.instructions p cn mn, i < 0]
isTarget _                                 = return False

-- | Checks the instruction of the current state is a PutField instruction.
maybePutField :: P.Program -> PState i a -> Maybe Address
maybePutField p (PState _ (Frame _ (_:RefVal q:_) cn mn pc:_) _)   = 
  case P.instruction p cn mn pc of
    P.PutField _ _ -> Just q
    _              -> Nothing
maybePutField _ _ = Nothing

-- | Maps a function over the annotations.
mapAnnotations :: MemoryModel a => (a -> a) -> PState i a -> PState i a
mapAnnotations f (PState hp frms ann) = PState hp frms (f ann)
mapAnnotations _ st                   = st

-- | Maps a value function over the frames.
mapValuesFS :: (AbstrValue i -> AbstrValue i) -> [Frame i] -> [Frame i]
mapValuesFS f = map (mapValuesF f) 

-- | Maps a value function over the state.
mapValues :: (AbstrValue i -> AbstrValue i) -> PState i a -> PState i a
mapValues f (PState hp frms ann) = PState (mapValuesH f hp) (map (mapValuesF f) frms) ann
mapValues _ st                   = st

-- | Substitutes a value in a state with another one.
-- Removes the entry in the heap if it the substituted value was a 'RefVal'.
substitute :: Eq i => AbstrValue i -> AbstrValue i -> PState i a -> PState i a
substitute v1@(RefVal adr1) v2 st = 
  let PState hp frms ann = mapValues (\v -> if v == v1 then v2 else v) st
  in  PState (deallocate adr1 hp) frms ann
substitute v1 v2 st = mapValues (\v -> if v == v1 then v2 else v) st


-- paths
-- TODO: computation should return (value,path) pairs.

-- | Returns rooted paths 'RPath' from a state.
rpaths :: PState i a -> [RPath]
rpaths (PState hp frms _) =
  concatMap rpahts' $ zip [0..] frms
  where
    rpahts' (m, Frame loc stk _ _ _ ) = 
      let nloc = zip [0..] (elemsL loc)
          nstk = zip [0..] (elemsS stk)
      in  concatMap (locpath m) nloc ++ concatMap (stkpath m) nstk
    locpath m (n,v) = RPath (RLoc m n) `map` valpath v
    stkpath m (n,v) = RPath (RStk m n) `map` valpath v
    valpath (RefVal q) = paths q hp
    valpath _          = [[]]
rpaths (EState _) = []

-- | Computes the value of a 'RPath'.
rpathValue :: (IntDomain i) => RPath -> PState i a -> AbstrValue i
rpathValue rpath st = 
  let (val,path) = 
        case rpath of
          RPath (RLoc m n) lpath -> (lookupL n . locals $ frames st !! m,lpath)
          RPath (RStk m n) spath -> (lookupS n . opstk  $ frames st !! m,spath)
  in case val of 
    RefVal q -> pathValue q path (heap st)
    _        -> val

-- | Checks if two 'RPath' has the same root.
rcommonRoot :: RPath -> RPath -> Bool
rcommonRoot (RPath r1 _) (RPath r2 _) = r1 == r2

-- | Computes a common prefix of two paths, if it exists, otherwise Nothing.
rcommonPrefix :: RPath -> RPath -> Maybe RPath
rcommonPrefix (RPath r1 ls1) (RPath r2 ls2) 
  | r1 == r2  = Just $ RPath r1 (commonPrefix ls1 ls2)
  | otherwise = Nothing

-- | Computes the maximal prefix of a 'RPath' in a list of 'RPath'.
rmaxPrefix :: RPath -> [RPath] -> RPath
rmaxPrefix path@(RPath r rls) pths = 
  RPath r (findFirst (reverse $ inits rls) (filterRoot path pths))
  where  
    filterRoot path1 paths2 = [  ls | path2@(RPath _ ls) <- paths2, rcommonRoot path1 path2]
    findFirst (l:ls) lss 
      | l `elem` lss = l
      | otherwise    = findFirst ls lss
    findFirst [] _ = []

-- | Returns the value from a given Frame index.
valueV :: P.Var -> PState i a -> AbstrValue i
valueV (P.StkVar i j) (PState _ frms _) = (reverse . opstk)  (reverse frms !! i) !! j
valueV (P.LocVar i j) (PState _ frms _) = locals (reverse frms !! i) !! j
{-valueV (LocVar i j) (PState _ frms _) = case lookup i $ zip [0..] frms of-}
  {-Nothing -> error $ "frms" ++ show (i, length frms)-}
  {-Just frm -> case lookup j $ zip [0..] (locals frm) of-}
    {-Nothing -> error $ "locals" ++ show (j,length (locals frm))-}
    {-Just v -> v-}


-- | Returns the type from a given Frame index.
typeV :: P.Var -> PState i a -> P.Type
typeV v st@(PState hp _ _) = case valueV v st of
  RefVal q -> P.RefType . className $ lookupH q hp
  w        -> fromJust $ typeOf w
 
-- | Computes reachable Addresses from a given a Frame index.
reachableV :: P.Var -> PState i a -> [Address]
reachableV var st = case valueV var st of
  RefVal r -> reachable r (heap st)
  _        -> []
    
-- | Returns the program location of a state.
programLocation :: PState i a -> [(P.ClassId,P.MethodId,P.PC)]
programLocation (PState _ frms _)  = [(cn,mn,pc) | Frame _ _ cn mn pc <- frms]
programLocation (EState _)         = []


-- | Returns the type of an address.
tyOf :: PState i a -> Address -> P.Type
tyOf st q = P.RefType . className $ lookupH q (heap st)


-- | Returns the kind of an address.
refKindOf :: PState i a -> Address -> P.RefKind
refKindOf st q = case lookupH q (heap st) of
  Instance cn _ -> P.InstanceKind cn
  AbsVar cn     -> P.ClassVarKind cn


