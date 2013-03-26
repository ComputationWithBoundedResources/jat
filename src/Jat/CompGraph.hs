module Jat.CompGraph where


import Jat.Constraints (Constraint)
import Jat.JatM
import Jat.PState
import qualified Jat.Constraints as C
import qualified Jat.Program as P

import Control.Applicative ((<|>))
import Data.Graph.Inductive

(<|>!) :: Maybe a -> a -> a
Just a  <|>! _ = a
Nothing <|>! a = a


-- finding instance/merge nodes for backjumps
-- assumptions: 
-- * code is unstructured, i.e. decomposition in general not possible
-- * if there are multiple candidates then one is the predecessor of the other one
--   i.e. c1 ->n -> c2 ->n e is valid but c1 ->n e, c2 ->n e, c1 /->n c2, c2 /-> c1 not
--   then predecessor is defined by wrt. to the transivity relation
-- finding a candidate reduces to (predc) topsort if we do not allow merging of nodes stemming from different back jump points

data ELabel     = EvaluationLabel Constraint | InstanceLabel | RefinementLabel Constraint deriving Show
type NLabel i a = PState i a

type JGraph i a   = Gr (NLabel i a) ELabel
type JContext i a = Context (NLabel i a) ELabel
-- 'MkGraph' consists of a Graph and a list of Contexts ('JContext'). A Context
-- corresponds to a (non-terminal) leaf node.
data MkGraph i a  = MkGraph (JGraph i a) [JContext i a]

mkGraph :: (Monad m, IntDomain i) => P.ClassId -> P.MethodId -> JatM m (MkGraph i a) 
mkGraph cn mn = mkInitialNode cn mn >>= mkSteps
  where mkInitialNode = undefined

state' :: JContext i a -> PState i a
state' = lab'

isTerminal' :: JContext i a -> Bool
isTerminal' (_,_,st,s) = null s && isTerminalState st

isBackJump' :: JContext i a -> Bool
isBackJump' (_,_,st,_) = undefined
-- use lab' ctx

isSimilar' :: JContext i a -> JContext i a -> Bool
isSimilar' (_,_,st1,_) (_,_,st2,_) = undefined

isInstance' :: JContext i a -> JContext i a -> Bool
isInstance' ctx1 ctx2 = undefined

join' :: Monad m => JContext i a -> JContext i a -> JatM m (PState i a)
join' ctx1 ctx2 = undefined

mkSteps :: (Monad m, IntDomain i) => MkGraph i a -> JatM m (MkGraph i a)
mkSteps mg@(MkGraph _ [])                               = return mg
mkSteps (MkGraph g (ctx1:ctx2:ctxs)) | isTerminal' ctx1 = return $ MkGraph g (ctx2:ctxs)
mkSteps mg                                              = mkStep mg >>= mkSteps

mkStep :: (Monad m, IntDomain i) => MkGraph i a -> JatM m (MkGraph i a) 
mkStep g = tryLoop g <|>! mkEval g


tryLoop :: Monad m => MkGraph i a -> Maybe (JatM m (MkGraph i a))
tryLoop (MkGraph _ [])                              = error "Jat.CompGraph.tryInstance: empty context."
tryLoop (MkGraph _ (ctx:_)) | not (isBackJump' ctx) = Nothing
tryLoop mg@(MkGraph g (ctx:_))                      = eval candidates
  where
    candidates        = do
      Just n <-  bfsWith (\lctx -> if isSimilar' ctx lctx then Just ctx else Nothing) (node' ctx) (grev g)
      return n
    eval ns | null ns = Nothing
    eval ns           = tryInstance nctx mg <|> Just (mkJoin nctx mg)
      where nctx = head ns

tryInstance :: Monad m => JContext i a -> MkGraph i a -> Maybe (JatM m (MkGraph i a))
tryInstance ctx2 mg@(MkGraph _ (ctx1:_)) | isInstance' ctx1 ctx2 = Just $ mkInstance ctx2 mg
tryInstance _ _                                                  = Nothing

mkInstance :: Monad m => JContext i a -> MkGraph i a -> JatM m (MkGraph i a)
mkInstance ctx2 (MkGraph g (ctx1:ctxs)) = return $ MkGraph g' ctxs
  where g' = insEdge (node' ctx2, node' ctx1, InstanceLabel) g
mkInstance _ _ = error "Jat.CompGraph.mkInstance: empty context."


mkJoin :: Monad m => JContext i a -> MkGraph i a -> JatM m (MkGraph i a)
mkJoin ctx2 (MkGraph g (ctx1:ctxs)) = do
  k   <- freshKey
  st3 <- join' ctx1 ctx2
  let edge = (InstanceLabel, node' ctx2)
      ctx3 = ([edge],k,st3,[])
      g1   = ctx3 & delNodes successors g
  return $ MkGraph g1 (ctx3: filter (\lctx -> node' lctx `elem` successors) ctxs)
  where  successors = dfs [node' ctx1] g
mkJoin _ _ = error "Jat.CompGraph.mkInstance: empty context."

mkEval :: (Monad m, IntDomain i) => MkGraph i a -> JatM m (MkGraph i a)
mkEval mg@(MkGraph _ (ctx:_)) = do
  let st = state' ctx 
  step <- exec st
  case step of
    Evaluation  e -> addNodes EvaluationLabel [e] mg
    Refinement rs -> addNodes RefinementLabel rs mg
    Abstraction a -> addNodes (const InstanceLabel) [a] mg

  where
    addNodes :: Monad m => (Constraint -> ELabel) -> [(PState i a, Constraint)] -> MkGraph i a -> JatM m (MkGraph i a)
    addNodes label rs (MkGraph g (origin:ctxs)) = foldM (addNode (node' origin)) (MkGraph g ctxs) rs
      where 
      addNode k1 (MkGraph g1 ctxs1) (st,con) = do
          k2 <- freshKey
          let edge = (label con, k1)
              ctx2 = ([edge],k2,st,[])
              g2   = ctx2 & g1
          return $ MkGraph g2 (ctx2:ctxs1)
    addNodes _ _ _ = error "Jat.CompGraph.mkEval: assertion error: unexpected case."

mkEval _ = error "Jat.CompGraph.mkEval: emtpy context."




