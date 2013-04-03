module Jat.PState.Fun
  (
    mkInstance
  , mkAbsInstance
  , mkGetField
  , mkPutField

  , isTerminal
  , isSimilar
  , isBackJump
  , isTarget

  , mapValues
  , substitute
  )
where

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
import qualified Jat.Program as P

import qualified Data.Array as A

mkInstance :: IntDomain i => P.Program -> P.ClassId -> Object i
mkInstance p cn = Instance cn (mkFt . initfds $ fds)
  where
    fds     = P.hasFields p cn
    initfds = map (\(lfn,lcn,ltp) -> (lcn,lfn,defaultValue ltp))
    mkFt    = foldl (flip $ curry3 updateFT) emptyFT
    curry3 f (a,b,c) = f a b c

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

mkGetField :: (MemoryModel a, IntDomain i) => PState i a -> P.ClassId -> P.FieldId -> PStep (PState i a)
mkGetField (PState _ (Frame _ (Null:_) _ _ _ :_) _) _ _ =  topEvaluation $ EState NullPointerException
mkGetField (PState hp (Frame loc (RefVal adr:stk) cn1 mn pc :frms) us) cn2 fn = 
  case lookupH adr hp of
    AbsVar _      -> error "Jat.PState.Fun.mkGetField: unexpected case."
    Instance _ ft -> let stk' = lookupFT cn2 fn ft :stk
                    in topEvaluation (PState hp (Frame loc stk' cn1  mn (pc+1) :frms) us)
mkGetField _ _ _ = error "Jat.PState.Fun.mkGetField: unexpected case"

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



isTerminal :: PState i a -> Bool
isTerminal (PState _ frms _) = null frms
isTerminal (EState _)        = True

isSimilar :: PState i a -> PState i a -> Bool
isSimilar (PState _ frms1 _) (PState _ frms2 _) = isSimilarFS frms1 frms2
  where
    isSimilarFS (f1:fs1) (f2:fs2) = isSimilarF f1 f2 && isSimilarFS fs1 fs2
    isSimilarFS [][]              = True
    isSimilarFS _ _               = False
    isSimilarF (Frame _ _ cn1 mn1 pc1) (Frame _ _ cn2 mn2 pc2) = 
      cn1 == cn2 && mn1 == mn2 && pc1 == pc2
isSimilar _ _ = False

isBackJump :: Monad m => PState i a -> JatM m Bool 
isBackJump (PState _ (Frame _ _ cn mn pc:_) _) = getProgram >>= \p -> return $ P.isBackJump p cn mn pc
isBackJump _                                   = return False

isTarget :: Monad m => PState i a -> JatM m Bool 
isTarget (PState _ (Frame _ _ cn mn pc:_) _) = do
  p <- getProgram
  return $ pc `elem` [ pc'+i | (pc', P.Goto i) <- A.assocs $ P.instructions p cn mn, i < 0]
isTarget _                                 = return False

mapValues :: (AbstrValue i -> AbstrValue i) -> PState i a -> PState i a
mapValues f (PState hp frms ann) = PState (mapValuesH f hp) (map (mapValuesF f) frms) ann
mapValues _ st                   = st

substitute :: Eq i => AbstrValue i -> AbstrValue i -> PState i a -> PState i a
substitute v1 v2 = mapValues (\v -> if v == v1 then v2 else v)

--elemsFS :: FrameStk i -> [AbstrValue i]
--elemsFS = concatMap elemsF

--addressesFS :: FrameStk i -> [Address]
--addressesFS fs = [q | RefVal q <- elemsFS fs]

--samePC :: PState i a -> PState i a -> Bool
--samePC (PState _ (Frame(_,_,_,_,pc):_) _) (PState _ (Frame(_,_,_,_,pc'):_) _) = pc == pc'


--isWTarget :: P.Program -> PState i a -> Bool
--isWTarget p (PState _ (Frame(_,_,cn,mn,pc):_) _) = P.isWTarget p cn mn pc
--isWTarget _ _                                    = error "isWTarget:empty frmstk"

--isWBranchOf :: P.Program -> PState i a -> PState i a -> Bool
--isWBranchOf p (PState _ (Frame(_,_,cn,mn,pc):_) _) (PState _ (Frame(_,_,_,_,pc'):_) _) = P.isWBranchOf p cn mn pc pc'
--isWBranchOf _ _ _                                  = error "isWBranch:empty frmstk"

--isFalseBranch :: P.Program -> PState i a -> Bool
--isFalseBranch p (PState _ (Frame(_,(BoolVal (Boolean False),_):_,_,_,_):_) _) = True
--isFalseBranch _ _ = False

--maybePutField :: P.Program -> PState i a -> Maybe Address
--maybePutField p (PState _ (Frame(_,v:(RefVal q,_):_,cn,mn,pc):_) _) = 
  --case P.instruction p cn mn pc of
    --P.PutField _ _ -> Just q
    --otherwise      -> Nothing
--maybePutField _ _ = Nothing


-- FIXME:rename
--isReturn :: P.Program -> PState i a -> Bool
--isReturn p (PState _ (frm1:frm2:frms) _ ) = False
--isReturn p (PState _ [Frame(_,_,cn,mn,pc)] _) = 
  --case P.instruction p cn mn pc of
    --P.Return  -> True
    --otherwise -> False

-- FIXME:
-- could be a problem if e.g. corresponding object in putfield is abstracted (abstraction<->refinement)
-- TODO:
-- would it be enough to abstract the predecessor of closing node
{-tryCycleAbstraction :: (IntDomain i) => P.Program -> PState i a -> Jat (Maybe (Step i a))-}
{-tryCycleAbstraction p s@(PState heap frms _) = -}
  {-return $ maybe Nothing (Just . cycleAbstraction p s) maybeCycle-}
  {-where maybeCycle =  anyJust (anyCycle heap) [r | RefVal r <- concatMap elemsF frms]-}

{-cycleAbstraction :: (IntDomain i) => P.Program -> PState i a -> Address -> Step i a-}
{-cycleAbstraction _ _ q | trace ("cycleabstraction" ++ show q) False = undefined-}
{-cycleAbstraction p (PState heap frms annot) q = abstraction $ PState (updateH q (AbsVar cn) heap) frms annot-}
  {-where cn = className (lookupH heap q)-}

-- FIXME : move to Utils
--anyJust :: (a -> Maybe b ) -> [a] -> Maybe b
--anyJust f [] = Nothing
--anyJust f (x:xs) = case f x of 
                     --Just b  -> Just b
                     --Nothing -> anyJust f xs

--isNull :: PState i a -> Bool
--isNull (PState _ (Frame(_,(Null,_):_,_,_,_):_) _) = True
--isNull _                                      = False



--evaluation :: PState i a -> Constraint -> Step i a
--evaluation = curry Evaluation

--refinement :: [(PState i a, Constraint)] -> Step i a
--refinement = Refinement

--abstraction :: PState i a -> Step i a
--abstraction = Abstraction
 
--step :: ((PState i a, Constraint) -> b) -> ([(PState i a, Constraint)] -> b) -> (PState i a -> b)  ->  Step i a -> b
--step f g h (Evaluation x)  = f x
--step f g h (Refinement xs) = g xs
--step f g h (Abstraction x) = h x

