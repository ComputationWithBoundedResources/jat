module Jat.PState.MemoryModel.Sharing
  (
  Sharing
  )
where

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
import Jat.Utils.Pretty
import Jat.Utils.Fun
import qualified Jat.Program as P

import qualified Data.Rewriting.Term as TRS (Term (..)) 

import Data.Maybe (fromMaybe)
import qualified Data.Map as M
import qualified Data.Set as S
import Control.Monad.State
import Control.Monad (zipWithM)
import Data.List (find)

import Debug.Trace



instance Pretty Var where
  pretty (LocVar i j) = text "lv" <> int i <> colon <> int j
  pretty (StkVar i j) = text "sv" <> int i <> colon <> int j

instance Show Var where
  show v = show $ pretty v

type NShares = PS.PairSet Address
type MShares = PS.PairSet Address
type TreeShs = S.Set Address

data Sharing = Sh (PS.PairSet Address) (PS.PairSet Var) (S.Set Var)

data Annot = Address :/=: Address | Address :><: Address |  TS Address

instance Pretty Annot where
  pretty (q:/=:r) = int q <> text "/=" <> int r
  pretty (q:><:r) = int q <> text "><" <> int r
  pretty (TS q)   = char '^' <> int q

nShares :: Sharing -> [Annot]
nShares (Sh ns _ _) = (:/=:) `map` PS.elems ns

mShares :: Sharing -> [Annot]
mShares (Sh _ ms _) = (:><:) `map` PS.elems ms

treeShs :: Sharing -> TreeShs
treeShs (Sh _ _ ts) = TS `map` S.elems ts 

liftNS :: (a -> b) -> Sharing -> Sharing
liftNS f (Sh ns ms ts) = Sh (f ns) ms ts

liftMS :: (a -> b) -> Sharing -> Sharing
liftMS f (Sh ns ms ts) = Sh ns (f ms) ts

liftTS :: (a -> b) -> Sharing -> Sharing
liftTS f (Sh ns ms ts) = Sh ns ms (f ts)

insertSh :: Annot -> Sharing -> Sharing
insertSh (q:/=:r) = liftNS (PS.insert (q,r))
insertSh (q:><:r) = liftMS (PS.insert (q,r))
insertSh (TS q)   = liftTS (S.insert  q)

memberSh :: Annot -> Sharing -> Bool
memberSh (q:/=:r) = PS.member (q,r) . nShares
memberSh (q:><:r) = PS.member (q,r) . mShares
memberSh (TS q)   = S.member q . treeShs

emptySh :: Sharing
emptySh = (Sh PS.empty PS.empty S.empty)

instance Pretty Sharing where
  pretty sh =
    (hsep . map pretty $ nShares sh)
    <$> (hsep . map pretty $ mShares sh)
    <$> (hsep . map pretty $ treeShs sh)

type Sh i = PState i Sharing

sharing :: Sh i -> Sharing
sharing (PState _ _ sh) = sh

tyOf :: P.Program -> Sh i -> Address -> P.Type
tyOf p st q = P.RefType . className $ lookupH q (heap st)

maybeShares :: P.Program -> Sh i -> Address -> Address -> Bool
maybeShares p st q r = P.areSharingTypes p (tyOf p st q)  && maybeSharesSh p st q r

maybeSharesSh :: P.Program -> Sh i -> Address -> Address -> Bool
maybeSharesSh p st q r = any shares (mShares $ sharing st)
  where shares (v:/=:w) = 
          (q `elem` vreaches && r `elem` wreaches) || 
          (q `elem` wreaches && r `elem` vreaches)
      where
        vReaches = reachableFS v st
        wReaches = reachableFS w st

treeShapedSh :: P.Program -> Sh i -> Address -> Bool
treeShapedSh p st q = any k (treeShs $ sharing st)
  where k (T v) = q `elem` reachableFS v st

treeShaped :: P.Program -> Sh i -> Address -> Bool
treeShaped p st q = 
  P.isTreeShapedType p (tyOf p st q) ||
  treeShapedSh st q
  


maybeCyclic :: P.Program -> Sh i -> Address -> Bool
maybeCyclic p st q = cyclicalType && not treeShaped
  where
    cyclicalType = P.isCyclicalType p (tyOf p st q)
    treeShaped = any (TreeShs $ sharing st)

maybeNotTreeShaped :: P.Program -> Sh i -> Address -> Bool
maybeNotTreeShaped p st q = not $ P.isTreeShapedType p (tyOf p st q)


mergeSh :: Sharing -> Sharing -> Sharing
mergeSh _ _ = Sh S.empty

unShare :: [Address] -> [Address] -> Sharing -> Sharing
unShare qs rs (Sh ns) = Sh $ foldl (flip S.insert) ns elems
  {-where elems = [ q:/=:r | q <- qs, r <- rs, q/=r ]-}
  where elems = []

memberSh :: NotShare -> Sharing -> Bool
memberSh ns (Sh sh) = ns `S.member` sh

nullify :: Address -> Sharing -> Sharing
nullify q (Sh ns) = Sh $ S.filter k ns
  where k (r1:/=:r2) = q /= r1 && q /= r2

substituteSh :: Eq i => AbstrValue i -> AbstrValue i -> Sh i -> Sh i
substituteSh v1 v2 st = case v1 of
  RefVal q -> mapAnnotations (nullify q) $ substitute v1 v2 st
  _        -> substitute v1 v2 st

mname :: String
mname = "Jat.PState.MemoryModel.Sharing"

merror :: String -> a
merror msg = error $ mname ++ msg


instance Pretty Sharing where 
  pretty (Sh ns) = hsep . map pretty $ S.elems ns

shares :: Address -> Address -> Sh i -> Bool
shares q r = not . sharesNot q r

sharesNot :: Address -> Address -> Sh i -> Bool
sharesNot q r = undefined

-- oh no we can only make a statement for those reachable in the current frame
-- others share per assumption if types share
-- extension in the anlysis is not easy
  

instance MemoryModel Sharing where
  new       = undefined
  getField  = undefined
  putField  = undefined

  invoke    = undefined
  equals    = undefined
  nequals   = undefined

  initMem   = undefined

  leq       = undefined
  join      = undefined

  normalize = undefined
  state2TRS = undefined

  {-new       = newSh-}
  {-getField  = getFieldSh-}
  {-putField  = putFieldSh-}

  {-invoke    = invokeSh-}
  {-equals    = equalsSh-}
  {-nequals   = nequalsSh-}

  {-initMem   = initMemSh-}

  {-leq       = leqSh-}
  {-join      = joinSh-}

  {-normalize = normalizeSh-}
  {-state2TRS = state2TRSSh-}


{--- TODO-}
{--- abstract common things-}
{--- newSh: only unsharing notations added-}
{--- getField = equal (given instancerefinement)-}
{--- tryInstanceRefinement : equalityrefinement can be ignored-}
{--- instanceRefinment : ignoring update sharing-}
{--- substituteSh equal-}
{--- invoke is equal-}
{--- initMem equal up to initialization of annot-}
  
{-newSh :: (Monad m, IntDomain i) => Sh i -> P.ClassId -> JatM m (PStep(Sh i))-}
{-newSh (PState hp (Frame loc stk cn mn pc :frms) sh) newcn = do-}
  {-p <- getProgram-}
  {-let obt       = mkInstance p newcn-}
      {-(adr,hp') = insertHA obt hp-}
      {-stk'      = RefVal adr :stk-}
      {-sh'       = unShare [adr] (addresses hp) sh-}
  {-return $ topEvaluation (PState hp' (Frame loc stk' cn mn (pc+1) :frms) sh')-}
{-newSh _ _ = merror ".new: unexpected case."-}


{-getFieldSh :: (Monad m, IntDomain i) => Sh i -> P.ClassId -> P.FieldId -> JatM m (PStep(Sh i))-}
{-getFieldSh st cn fn | trace (show cn) False = undefined-}
{-getFieldSh st cn fn = case opstk $ frame st of-}
  {-Null :_        -> return $ topEvaluation (EState NullPointerException)-}
  {-RefVal adr : _ -> tryInstanceRefinement st adr |>> return (mkGetField st cn fn)-}
  {-_              -> error $ mname ++ ".getField: unexpected case."-}

{-putFieldSh :: (Monad m, IntDomain i) => Sh i -> P.ClassId -> P.FieldId -> JatM m (PStep(Sh i))-}
{-putFieldSh st@(PState _ _ sh) cn fn = case opstk $ frame st of-}
  {-_ : Null       : _ -> return $ topEvaluation (EState NullPointerException)-}
  {-_ : RefVal adr : _ -> tryInstanceRefinement st adr -}
                       {-|> tryEqualityRefinement st adr-}
                       {-|>> mkPutField sh st cn fn-}
  {-_                  -> merror ".getField: unexpected case."-}

{-invokeSh :: (Monad m, IntDomain i) => Sh i -> P.MethodId -> Int -> JatM m (PStep(Sh i))-}
{-invokeSh st1 mn1 n1 = do-}
  {-p <- getProgram-}
  {-invoke' p st1 mn1 n1-}
  {-where-}
    {-invoke' p st@(PState hp (Frame loc stk fcn fmn pc :frms) sh) mn n =-}
      {-case rv  of-}
        {-Null     -> return . topEvaluation $ EState NullPointerException-}
        {-RefVal q -> tryInstanceRefinement st q-}
                  {-|>> return (topEvaluation $ PState hp (frm:Frame loc stk2 fcn fmn pc:frms) sh)-}
        {-_        -> merror ".invoke: invalid type on stack"-}
      {-where-}
        {-(ps,stk1)   = splitAt n stk-}
        {-([rv],stk2) = splitAt 1 stk1-}
        {-cn1         = className $ lookupH (theAddress rv) hp-}
        {-(cn2,mb)    = P.seesMethodIn p cn1 mn-}
        {-mxl         = P.maxLoc mb-}
        {-frm         = Frame (initL (rv:reverse ps) mxl) [] cn2 mn 0-}
    {-invoke' _ _ _ _ = error ".inoke: exceptional case."-}

{-tryInstanceRefinement :: (Monad m, IntDomain i) => Sh i -> Address -> JatM m (Maybe (PStep(Sh i)))-}
{-tryInstanceRefinement st@(PState hp _ _) q = case lookupH q hp of-}
    {-AbsVar _     -> getProgram >>= \p -> Just `liftM` instanceRefinement p st q-}
    {-Instance _ _ -> return Nothing-}
{-tryInstanceRefinement _ _ = merror ".tryInstanceRefinement: exceptional case."-}


{-instanceRefinement :: (Monad m, IntDomain i) => P.Program -> Sh i -> Address -> JatM m (PStep(Sh i))-}
{-instanceRefinement p st@(PState hp frms sh) adr = do-}
  {-instances <- instancesM-}
  {-nullref   <- nullM-}
  {-return . topRefinement $ nullref:instances-}
  {-where-}
    {-cns  = P.subClassesOf p . className $ lookupH adr hp-}
    {-obtM = mapM (mkAbsInstance hp adr) cns-}

    {-instancesM = map mkInstanceM `liftM` obtM-}
      {-where mkInstanceM (hp1,obt1) = let hp2 = updateH adr obt1 hp1 in PState hp2 frms sh-}
    {-nullM      = return $ substituteSh (RefVal adr) Null st-}

{-[>tryCyclicAbstraction :: Sh i -> Address -> JatM m (Maybe(PStep(Sh i)))<]-}
{-[>tryCyclicAbstraction st q = do<]-}
  {-[>p <- getProgram<]-}
  {-[>if maybeCyclic p st q <]-}
    {-[>then Just `liftM` cyclicAbstraction st q <]-}
    {-[>else return Nothing<]-}


{-tryEqualityRefinement :: (Monad m, IntDomain i) => Sh i -> Address -> JatM m (Maybe(PStep(Sh i)))-}
{-tryEqualityRefinement st q | trace ("tryEquality: " ++ show q) False = undefined-}
{-tryEqualityRefinement st@(PState hp fms sh) q = do -}
  {-p <- getProgram-}
  {-case find (maybeEqual p st q) (addresses hp) of-}
    {-Just r  -> Just `liftM` equalityRefinement st q r-}
    {-Nothing -> return Nothing-}

{-equalityRefinement :: (Monad m, IntDomain i) => Sh i -> Address -> Address -> JatM m (PStep(Sh i))-}
{-equalityRefinement st q r | trace ("doEquality: " ++ show (r,q)) False = undefined-}
{-equalityRefinement st@(PState hp frms sh) r q = do-}
  {-p <- getProgram-}
  {-return . topRefinement $ if leqSh p mkEqual st then [mkEqual, mkNequal] else [mkNequal]-}
  {-where-}
    {-mkEqual  = substituteSh (RefVal q) (RefVal r) st-}
    {-mkNequal = PState hp frms (r:/=:q `insertNs` sh) -}

{-maybeEqual :: IntDomain i => P.Program -> Sh i -> Address -> Address -> Bool-}
{-maybeEqual p st@(PState hp (frm:frms) sh) q r = and $ -}
  {-let t = -}
        {-[ q/=r-}
        {-, maybeShare p st r q -}
        {-, not $ (r:/=:q) `memberNs` sh-}
        {-]-}
  {-in trace (show (pcounter frm,q,r,t)) t-}

{-equalsSh :: (Monad m, IntDomain i) => Sh i -> JatM m (PStep(Sh i))-}
{-equalsSh st@(PState hp (Frame loc (v1:v2:stk) cn mn pc :frms) sh) =-}
  {-getProgram >>= \p -> equalsx p v1 v2-}
  {-where-}
    {-equalsx p (RefVal q) (RefVal r) | q == r = mkBool True-}
    {-equalsx p (RefVal q) (RefVal r) | (q:/=:r) `memberSh` sh = mkBool False-}
    {-equalsx p (RefVal q) (RefVal r) = -}
      {-if maybeEqual p st q r-}
         {-then equalityRefinement st q r-}
         {-else mkBool False-}
    {-equalsx p (RefVal q) Null = -}
      {-tryInstanceRefinement st q |>> mkBool False-}
    {-equalsx p Null (RefVal r) =-}
      {-tryInstanceRefinement st r |>> mkBool False-}
    {-equalsx p _ _ = merror ".equals: unexpected case."-}
    {-mkBool b = return . topEvaluation $ PState hp (Frame loc stk' cn mn (pc+1):frms) sh-}
      {-where stk' = BoolVal (AD.constant b) : stk-}
{-equalsSh _ = merror ".equals: exceptional case."-}

{-nequalsSh :: (Monad m, IntDomain i) => Sh i -> JatM m (PStep(Sh i))-}
{-nequalsSh st@(PState hp (Frame loc (v1:v2:stk) cn mn pc :frms) sh) =-}
  {-getProgram >>= \p -> nequalsx p v1 v2-}
  {-where-}
    {-nequalsx _ (RefVal q) (RefVal r) | q == r = mkBool False-}
    {-nequalsx _ (RefVal q) (RefVal r) | (q:/=:r) `memberSh` sh = mkBool True-}
    {-nequalsx p (RefVal q) (RefVal r) = -}
      {-if maybeEqual p st q r-}
         {-then equalityRefinement st q r-}
         {-else mkBool True-}
    {-nequalsx _ (RefVal q) Null = -}
      {-tryInstanceRefinement st q |>> mkBool True-}
    {-nequalsx _ Null (RefVal r) =-}
      {-tryInstanceRefinement st r |>> mkBool True-}
    {-nequalsx _ _ _ = merror ".nequals: unexpected case."-}
    {-mkBool b = return . topEvaluation $ PState hp (Frame loc stk' cn mn (pc+1):frms) sh-}
      {-where stk' = BoolVal (AD.constant b) : stk-}
{-nequalsSh _ = merror ".nequals: exceptional case."-}

{-initMemSh :: (Monad m, IntDomain i) => P.ClassId -> P.MethodId -> JatM m (Sh i)-}
{-initMemSh cn mn = do-}
  {-p <- getProgram-}
  {-let m = P.theMethod p cn mn-}
  {-(hp1,_)      <- mkAbsInstance emptyH 0 cn-}
  {-(hp2,params) <- foldM defaultAbstrValue (hp1,[]) (P.methodParams m)-}
  {-let loc = initL (RefVal 0:params) $ P.maxLoc m-}
  {-return $ PState hp2 [Frame loc [] cn mn 0] (initSh (addresses hp2))-}
  {-where-}
    {-defaultAbstrValue (hp,params) ty = case ty of-}
      {-P.BoolType    -> AD.top >>= \b -> return (hp, params++[BoolVal b])-}
      {-P.IntType     -> AD.top >>= \i -> return (hp, params++[IntVal i])-}
      {-P.NullType    ->                  return (hp, params++[Null])-}
      {-P.Void        ->                  return (hp, params++[Unit])-}
      {-P.RefType cn' ->                  return (hp',params++[RefVal r])-}
        {-where (r, hp') = insertHA (AbsVar cn') hp-}
    {-initSh as = unShare as as emptySh-}

{-newtype M = M {   -}
    {-unMorph      :: M.Map Address Address-}
  {-}-}
{-type Morph = State M-}

{-emptyMorph :: M-}
{-emptyMorph = M{unMorph=M.empty}-}

{-withMorph :: (M.Map Address Address -> M.Map Address Address) -> Morph a -> Morph a-}
{-withMorph f = withState (\x -> x{unMorph=f(unMorph x)})-}

{-modifyMorph :: (M.Map Address Address -> M.Map Address Address) -> Morph ()-}
{-modifyMorph f = modify $ \x -> x{unMorph=f(unMorph x)}-}


{-leqSh :: IntDomain i => P.Program -> Sh i -> Sh i -> Bool-}
{-leqSh p (PState hp1 frms1 sh1) (PState hp2 frms2 sh2) = -}
  {-let (leqFrms,morph) = runState runFrms emptyMorph in-}
  {-let b1 = leqFrms -}
      {-b2 = mapit (unMorph morph) (nShares sh2) `S.isSubsetOf` nShares sh1-}
  {-in trace ("leq" ++ show (pcounter $ head frms1,b1,b2)) b1 && b2-}
  {-where-}
    {-[>runFrms = and `liftM` zipWithM leqValM (concatMap elemsF frms1) (concatMap elemsF frms2)<]-}
    {-runFrms = do-}
      {-bs <- zipWithM leqValM (concatMap elemsF frms1) (concatMap elemsF frms2)-}
      {-return $ trace (show bs) and bs-}
    {-mapit m = S.fold k S.empty-}
      {-where -- there exist no mapping when null<=absvarcn-}
        {-k (q:/=:r) = case (M.lookup q m, M.lookup r m) of-}
          {-(Just q', Just r') -> S.insert (q':/=:r')-}
          {-_                  -> id-}

    {-leqValM :: IntDomain i => AbstrValue i -> AbstrValue i -> Morph Bool-}
    {-[>leqValM v1 v2 | trace (show (v1,v2)) False = undefined<]-}
    {-leqValM (RefVal q) (RefVal r)  = do-}
      {-mapping <- gets unMorph-}
      {--- mapping from st2 to st1-}
      {-case M.lookup r mapping of-}
        {-Just q' -> return $ q==q'-}
        {-Nothing -> do-}
          {-modifyMorph (M.insert r q)-}
          {-leqObjM (lookupH q hp1) (lookupH r hp2)-}

    {-leqValM (BoolVal a) (BoolVal b) = return $ a `AD.leq` b-}
    {-leqValM (IntVal i)  (IntVal j)  = return $ i `AD.leq` j-}
    {-leqValM Unit _                  = return True-}
    {-leqValM Null Null               = return True-}
    {-leqValM Null (RefVal r)-}
      {-| not (isInstance (lookupH r hp2)) = return True-}
    {-leqValM _ _                     = return False-}

    {-leqObjM :: IntDomain i => Object i -> Object i -> Morph Bool-}
    {-leqObjM (Instance cn ft) (Instance cn' ft') = (cn == cn' &&) `liftM`  leqFtM ft ft'-}
    {-leqObjM (Instance cn _) (AbsVar cn')        = return $ P.isSuber p cn cn'-}
    {-leqObjM (AbsVar cn) (AbsVar cn')            = return $ P.isSuber p cn cn'-}
    {-leqObjM _ _                                 = return False-}

    {-leqFtM :: IntDomain i => FieldTable i -> FieldTable i -> Morph Bool-}
    {-leqFtM ft ft' = and `liftM` zipWithM leqValM (elemsFT ft) (elemsFT ft')-}

{--- Todo: take correlation into account-}
{-joinSh :: (Monad m, IntDomain i) => Sh i -> Sh i -> JatM m (Sh i)-}
{-joinSh st1 st2 = do-}
  {-p <- getProgram-}
  {-mergeStates p st1 st2 (Sh S.empty)-}


{-[>unifiesObjectsM :: IntDomain i => P.Program -> PState i Sharing -> PState i Sharing -> Object i -> Object i -> Morph Bool<]-}
{-[>[>unifiesOjects b p s t o1 o2 | trace (">>> unifiesO\n" ++ (show $ pretty o1 <+> pretty o2)) False = undefined<]<]-}
{-[>unifiesObjectsM p s t (Instance cn ft) (Instance cn' ft') = (cn == cn' &&) `liftM`  unifiesFTablesM p s t ft ft'<]-}
{-[>unifiesObjectsM p _ _ (AbsVar cn) (Instance cn' _)        = return $ P.isSuper p cn cn'<]-}
{-[>unifiesObjectsM p _ _ (AbsVar cn) (AbsVar cn')            = return $ P.isSuper p cn cn'<]-}
{-[>unifiesObjectsM _ _ _ _ _                                 = return False<]-}

{-[>unifiesFTablesM :: IntDomain i => P.Program -> PState i Sharing -> PState i Sharing -> FieldTable i -> FieldTable i -> Morph Bool<]-}
{-[>unifiesFTablesM p s t ft ft' = and `liftM` zipWithM (unifiesValuesM p s t) (elemsFT ft) (elemsFT ft')<]-}

{-state2TRSSh :: (Monad m, IntDomain i) => Maybe Address -> Sh i -> Int -> JatM m (TRS.Term String String)-}
{-state2TRSSh m st@(PState hp _ sh) = pState2TRS isSpecial isJoinable m st-}
  {-where-}
    {-isSpecial adr        = True-}
    {-isJoinable adr1 adr2 = True-}
{-state2TRSSh m st = pState2TRS undefined undefined m st-}

{-normalizeSh = id-}

