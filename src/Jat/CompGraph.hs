module Jat.CompGraph 
  (
    MkJGraph
  , mkJGraph
  , mkJGraph2Dot
  --, mkGraph2TRS
  )
where


import Jat.Constraints (Constraint)
import Jat.JatM
import Jat.PState
import qualified Jat.Program as P
import Jat.Utils.Pretty

import Control.Applicative ((<|>))
import Data.Graph.Inductive
import Data.GraphViz.Types.Canonical
import qualified Data.GraphViz.Attributes.Complete as GV
import qualified Data.Text.Lazy as T

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
instance Pretty ELabel where pretty = text . show

type JGraph i a   = Gr (NLabel i a) ELabel
type JContext i a = Context (NLabel i a) ELabel
-- 'MkJGraph' consists of a Graph and a list of Contexts ('JContext'). A Context
-- corresponds to a (non-terminal) leaf node.
data MkJGraph i a  = MkJGraph (JGraph i a) [JContext i a]

mkJGraph :: (Monad m, IntDomain i) => P.ClassId -> P.MethodId -> JatM m (MkJGraph i a) 
mkJGraph cn mn = mkInitialNode cn mn >>= mkSteps
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

mkSteps :: (Monad m, IntDomain i) => MkJGraph i a -> JatM m (MkJGraph i a)
mkSteps mg@(MkJGraph _ [])                               = return mg
mkSteps (MkJGraph g (ctx1:ctx2:ctxs)) | isTerminal' ctx1 = return $ MkJGraph g (ctx2:ctxs)
mkSteps mg                                              = mkStep mg >>= mkSteps

mkStep :: (Monad m, IntDomain i) => MkJGraph i a -> JatM m (MkJGraph i a) 
mkStep g = tryLoop g <|>! mkEval g


tryLoop :: Monad m => MkJGraph i a -> Maybe (JatM m (MkJGraph i a))
tryLoop (MkJGraph _ [])                              = error "Jat.CompGraph.tryInstance: empty context."
tryLoop (MkJGraph _ (ctx:_)) | not (isBackJump' ctx) = Nothing
tryLoop mg@(MkJGraph g (ctx:_))                      = eval candidates
  where
    eval ns | null ns = Nothing
    eval ns           = tryInstance nctx mg <|> Just (mkJoin nctx mg)
      where nctx = head ns
    candidates = do
      Just n <-  bfsWith (condition ctx) (node' ctx) (grev g)
      return n
    condition ctx1 ctx2 = 
      if isSimilar' ctx1 ctx2 && null [ undefined | (_,_,RefinementLabel _) <- inn' ctx2] then Just ctx2 else Nothing


tryInstance :: Monad m => JContext i a -> MkJGraph i a -> Maybe (JatM m (MkJGraph i a))
tryInstance ctx2 mg@(MkJGraph _ (ctx1:_)) | isInstance' ctx1 ctx2 = Just $ mkInstance ctx2 mg
tryInstance _ _                                                  = Nothing

mkInstance :: Monad m => JContext i a -> MkJGraph i a -> JatM m (MkJGraph i a)
mkInstance ctx2 (MkJGraph g (ctx1:ctxs)) = return $ MkJGraph g' ctxs
  where g' = insEdge (node' ctx2, node' ctx1, InstanceLabel) g
mkInstance _ _ = error "Jat.CompGraph.mkInstance: empty context."


mkJoin :: Monad m => JContext i a -> MkJGraph i a -> JatM m (MkJGraph i a)
mkJoin ctx2 (MkJGraph g (ctx1:ctxs)) = do
  k   <- freshKey
  st3 <- join' ctx1 ctx2
  let edge = (InstanceLabel, node' ctx2)
      ctx3 = ([edge],k,st3,[])
      g1   = ctx3 & delNodes successors g
  return $ MkJGraph g1 (ctx3: filter (\lctx -> node' lctx `elem` successors) ctxs)
  where  successors = dfs [node' ctx1] g
mkJoin _ _ = error "Jat.CompGraph.mkInstance: empty context."

mkEval :: (Monad m, IntDomain i) => MkJGraph i a -> JatM m (MkJGraph i a)
mkEval mg@(MkJGraph _ (ctx:_)) = do
  let st = state' ctx 
  step <- exec st
  case step of
    Evaluation  e -> addNodes EvaluationLabel [e] mg
    Refinement rs -> addNodes RefinementLabel rs mg
    Abstraction a -> addNodes (const InstanceLabel) [a] mg

  where
    addNodes :: Monad m => (Constraint -> ELabel) -> [(PState i a, Constraint)] -> MkJGraph i a -> JatM m (MkJGraph i a)
    addNodes label rs (MkJGraph g (origin:ctxs)) = foldM (addNode (node' origin)) (MkJGraph g ctxs) rs
      where 
      addNode k1 (MkJGraph g1 ctxs1) (st,con) = do
          k2 <- freshKey
          let edge = (label con, k1)
              ctx2 = ([edge],k2,st,[])
              g2   = ctx2 & g1
          return $ MkJGraph g2 (ctx2:ctxs1)
    addNodes _ _ _ = error "Jat.CompGraph.mkEval: assertion error: unexpected case."

mkEval _ = error "Jat.CompGraph.mkEval: emtpy context."

mkJGraph2Dot :: (Pretty a,IntDomain i) => MkJGraph i a -> DotGraph Int
mkJGraph2Dot (MkJGraph g _) = 
  DotGraph { 
    strictGraph     = True
  , directedGraph   = True
  , graphID         = Just (Str $ T.pack "g")
  , graphStatements = DotStmts {
      attrStmts = []
    , subGraphs = []
    , nodeStmts = reverse . map mkCNode $ labNodes g
    , edgeStmts = reverse . map mkCEdge $ labEdges g
    }
  }
  where
    mkCNode (k,st) = 
      DotNode {
        nodeID = k
      , nodeAttributes = [
          GV.Label (GV.StrLabel . T.pack . display $ text "state:" <+> int k <$> pretty st)
        , GV.Shape GV.BoxShape
        ]
      }
    mkCEdge (k1,k2,l) = 
      DotEdge {
            fromNode       = k1
          , toNode         = k2
          , edgeAttributes = [
              GV.Label (GV.StrLabel $ T.pack $ display $ pretty l)
            ]
          }

