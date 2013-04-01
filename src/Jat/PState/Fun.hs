module Jat.PState.Fun
  (
    isTerminal
  , isSimilar
  , isBackJump
  , isTarget
  )
where

import Jat.PState.Data
import Jat.PState.Frame
import Jat.JatM
import qualified Jat.Program as P

import qualified Data.Array as A

isTerminal :: PState i a -> Bool
isTerminal (PState _ frms) = null frms
isTerminal (EState _)      = True

isSimilar :: PState i a -> PState i a -> Bool
isSimilar (PState _ frms1) (PState _ frms2) = isSimilarFS frms1 frms2
  where
    isSimilarFS (f1:fs1) (f2:fs2) = isSimilarF f1 f2 && isSimilarFS fs1 fs2
    isSimilarFS [][]              = True
    isSimilarFS _ _               = False
    isSimilarF (Frame _ _ cn1 mn1 pc1) (Frame _ _ cn2 mn2 pc2) = 
      cn1 == cn2 && mn1 == mn2 && pc1 == pc2
isSimilar _ _ = False

isBackJump :: Monad m => PState i a -> JatM m Bool 
isBackJump (PState _ (Frame _ _ cn mn pc:_)) = getProgram >>= \p -> return $ P.isBackJump p cn mn pc
isBackJump _                                 = return False

isTarget :: Monad m => PState i a -> JatM m Bool 
isTarget (PState _ (Frame _ _ cn mn pc:_)) = do
  p <- getProgram
  return $ pc `elem` [ pc'+i | (pc', P.Goto i) <- (A.assocs $ P.instructions p cn mn), i < 0]
isTarget _                                 = return False


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

--mapValues :: (AbstrValue i -> AbstrValue i) -> PState i a -> PState i a
--mapValues f (PState heap frms annot) = PState (mapValuesH f heap ) (map (mapValuesF f) frms) annot

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

