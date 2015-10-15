-- | This module provides the type and the rules for building the computation graph.
-- Refinement and evaluation steps depend on the (abstract) semantics.
-- Strategies for finding instances are should be implemented here.
module Jat.CompGraph 
  (
    MkJGraph
  , JGraph
  , mkJGraph
  , mkJGraph2Dot
  , mkJGraph2TRS
  , mkJGraphIO

  , simplifySCC
  )
where


import Jat.Constraints (PAFun, PAVar, PATerm, isTop)
import Jat.JatM
import Jat.PState
import Jat.Utils.Dot
import Jat.Utils.Fun
import Jat.Utils.Pretty as PP
import qualified Jinja.Program as P

import Data.Rewriting.Rule (Rule (..))

import Control.Monad.State (liftIO)
import Data.Graph.Inductive as Gr
import Data.GraphViz.Types.Canonical
import Data.Maybe (fromMaybe)
import System.IO (hFlush,stdout)
import qualified Control.Exception as E
import qualified Data.GraphViz.Attributes.Complete as GV
import qualified Data.Text.Lazy as T
import Data.List ((\\))
--import Debug.Trace

-- finding instance/merge nodes for backjumps
-- assumptions: 
-- * code is unstructured, i.e. decomposition in general not possible
-- * if there are multiple candidates then one is the predecessor of the other one
--   i.e. c1 ->n -> c2 ->n e is valid but c1 ->n e, c2 ->n e, c1 /->n c2, c2 /-> c1 not
--   then predecessor is defined by wrt. to the transivity relation
-- finding a candidate reduces to (predc) topsort if we do not allow merging of nodes stemming from different back jump points

data ELabel = 
    EvaluationLabel PATerm P.Instruction
  | InstanceLabel 
  | RefinementLabel PATerm
  deriving Show

instance Pretty ELabel where
  pretty (EvaluationLabel fm ins) = pretty fm <> colon <> pretty ins
  pretty (RefinementLabel fm)     = pretty fm
  pretty l                        = text $ show l
type NLabel i a = PState i a

type JGraph i a   = Gr (NLabel i a) ELabel
-- | A 'JContext' corresponds to a (non-terminal) leaf node.
type JContext i a = Context (NLabel i a) ELabel

-- | The type of the compuation graph.
data MkJGraph i a  = MkJGraph (JGraph i a) [JContext i a]

-- | Builds the computation graph, given class name and method name.
mkJGraph :: (Monad m, IntDomain i, MemoryModel a) => P.ClassId -> P.MethodId -> JatM m (MkJGraph i a) 
mkJGraph cn mn = mkInitialNode cn mn >>= mkSteps

mkInitialNode :: (Monad m, IntDomain i, MemoryModel a) => P.ClassId -> P.MethodId -> JatM m (MkJGraph i a)
mkInitialNode cn mn = do
  k <- freshKey
  st <- mkInitialState cn mn
  let ctx = ([],k,st,[]) 
      g   = ctx & Gr.empty
  return $ MkJGraph g [ctx]


mkSteps :: (Monad m, IntDomain i, MemoryModel a) => MkJGraph i a -> JatM m (MkJGraph i a)
mkSteps mg@(MkJGraph _ [])                        = return mg
mkSteps mg                                        = mkStep mg >>= mkSteps

-- a single step constitues of
-- * finding a merge node
-- * if non can be found make an evaluation step
mkStep :: (Monad m, IntDomain i, MemoryModel a) => MkJGraph i a -> JatM m (MkJGraph i a) 
mkStep (MkJGraph g (ctx:ctxs)) | isTerminal' ctx = return $ MkJGraph g ctxs
mkStep g                                         = tryLoop g |>> mkEval g


state' :: JContext i a -> PState i a
state' = lab'

instruction' :: P.Program -> JContext i a -> P.Instruction
instruction' p = instruction p . state'

isTerminal' :: JContext i a -> Bool
isTerminal' (_,_,st,s) = null s && isTerminal st

isTarget' :: Monad m => JContext i a -> JatM m Bool
isTarget' = isTarget . state'

isSimilar' :: JContext i a -> JContext i a -> Bool
isSimilar' ctx1 ctx2 = isSimilar (state' ctx1) (state' ctx2)

leq' :: (Monad m, IntDomain i, MemoryModel a) => JContext i a -> JContext i a -> JatM m Bool
leq' ctx1 ctx2 = getProgram >>= \p -> return $ leq p (state' ctx1) (state' ctx2)

join' :: (Monad m, IntDomain i, MemoryModel a) => JContext i a -> JContext i a -> JatM m (PState i a)
join' ctx1 ctx2 = lub (state' ctx1) (state' ctx2)


-- if a similar predecessor can be found then try to make an instance node, if not possible join the nodes
tryLoop :: (Monad m, IntDomain i, MemoryModel a) => MkJGraph i a -> JatM m (Maybe (MkJGraph i a))
tryLoop (MkJGraph _ [])          = error "Jat.CompGraph.tryInstance: empty context."
tryLoop mg@(MkJGraph g (ctx:_))  = do
  b <- isTarget' ctx
  if b then eval candidate else return Nothing
  where
    eval Nothing  = return Nothing
    eval (Just n) = Just `liftM` (tryInstance nctx mg |>> (mkJoin nctx mg >>= mkEval))
      where nctx = context g n
    candidate = rdfsnWith (condition ctx) (pre' ctx) g
    condition ctx1 ctx2 =
      isSimilar' ctx1 ctx2 && null [ undefined | (_,_,RefinementLabel _) <- inn' ctx2]
    
-- perform a backwards dfs wrt to minimum predecessor
-- if nodes are not merge nodes they have only one predecessor
-- if the node is a merge node then we follow the node with minimum key
rdfsnWith :: (JContext i a -> Bool) -> [Node] -> JGraph i a -> Maybe Node
rdfsnWith _ _      g | isEmpty g = Nothing
rdfsnWith _ []     _             = Nothing
rdfsnWith f (v:vs) g             = case match v g of
  (Just c , g') -> if f c then Just (node' c) else rdfsnWith f (predi c ++ vs) g'
  (Nothing, g') -> rdfsnWith f vs g'
  where
    predi ctx = [ n | n <- minNode $ pre' ctx, n < node' ctx]
      where 
        minNode [] = []
        minNode l  = [minimum l]
      
tryInstance :: (Monad m, IntDomain i, MemoryModel a) => JContext i a -> MkJGraph i a -> JatM m (Maybe (MkJGraph i a))
--tryInstance ctx2 (MkJGraph _ (ctx1:_)) | trace (">>> tryInstance: " ++ show (ctx2,ctx1)) False = undefined
tryInstance ctx2 mg@(MkJGraph _ (ctx1:_)) = do
  b <- leq' ctx1 ctx2
  if b then Just `liftM` mkInstanceNode ctx2 mg else return Nothing
tryInstance _ _ = return Nothing

mkInstanceNode :: Monad m => JContext i a -> MkJGraph i a -> JatM m (MkJGraph i a)
mkInstanceNode ctx2 (MkJGraph g (ctx1:ctxs)) = return $ MkJGraph g' ctxs
  where g' = insEdge (node' ctx1, node' ctx2, InstanceLabel) g
mkInstanceNode _ _ = error "Jat.CompGraph.mkInstance: empty context."


-- make and integrate a join node
-- nodes and contexts are suitably removed
mkJoin :: (Monad m, IntDomain i, MemoryModel a) => JContext i a -> MkJGraph i a -> JatM m (MkJGraph i a)
--mkJoin ctx2 (MkJGraph _ (ctx1:_)) | trace (">>> mkJoin: \n" ++ show (ctx2,ctx1)) False = undefined
mkJoin ctx2 (MkJGraph g (ctx1:ctxs)) = do
  k   <- freshKey
  st3 <- join' ctx1 ctx2
  let edge = (InstanceLabel, node' ctx2)
      ctx3 = ([edge],k,st3,[])
      g1  = delNodes successors g
      g2   = ctx3 & g1
      {-g2   = ctx3 & g-}
  return $ MkJGraph g2 (ctx3: filter (\lctx -> node' lctx `notElem` successors) ctxs)
  {-return $ MkJGraph g2 (ctx3: ctxs)-}
  where 
    ctxn = node' ctx2
    successors = dfsUntil ((<= ctxn) .  node') (suc' ctx2) g
    
mkJoin _ _ = error "Jat.CompGraph.mkInstance: empty context."

dfsUntil :: (JContext i a -> Bool) -> [Node] -> JGraph i a -> [Node]
dfsUntil _ _      g | isEmpty g = []
dfsUntil _ []     _             = []
dfsUntil f (v:vs) g             = case match v g of
  (Just c , g') -> if f c then dfsUntil f vs g' else node' c : dfsUntil f (suc' c ++ vs) g'
  (Nothing, g') -> dfsUntil f vs g'


mkEval :: (Monad m, IntDomain i, MemoryModel a) => MkJGraph i a -> JatM m (MkJGraph i a)
mkEval mg@(MkJGraph _ (ctx:_)) = do
  p <- getProgram
  let st  = state' ctx
      ins = instruction' p ctx
  step <- exec st
  case step of
    Evaluation  e -> addNodes (flip EvaluationLabel ins) [e] mg
    Refinement rs -> addNodes RefinementLabel rs mg
    Abstraction a -> addNodes (const InstanceLabel) [a] mg

  where
    addNodes :: Monad m => (PATerm -> ELabel) -> [(PState i a, PATerm)] -> MkJGraph i a -> JatM m (MkJGraph i a)
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

-- | Returns the Dot representation of a constructed computation graph..
mkJGraph2Dot :: (Pretty a,IntDomain i) => MkJGraph i a -> DotGraph Int
mkJGraph2Dot (MkJGraph g ctxs) = 
  DotGraph { 
    strictGraph     = True
  , directedGraph   = True
  , graphID         = Just (Str $ T.pack "g")
  , graphStatements = DotStmts {
      attrStmts = []
    , subGraphs = []
    , nodeStmts = map mkCNode (labNodes g) ++ map (mkCtxNode . labNode') ctxs
    , edgeStmts = map mkCEdge $ labEdges g
    }
  }
  where
    mkCNode (k,st) = 
      DotNode {
        nodeID = k
      , nodeAttributes = [
          GV.Label (GV.StrLabel . T.pack . display $ text "s" <> int k PP.<$> pretty st)
        , GV.Shape GV.BoxShape
        ]
      }
    mkCtxNode (k,st) = 
      DotNode {
        nodeID = -k
      , nodeAttributes = [
          GV.Label (GV.StrLabel . T.pack . display $ text "s" <> int k PP.<$> pretty st)
        , GV.Shape GV.BoxShape
        ]
      }
    mkCEdge (k1,k2,l) = 
      DotEdge {
            fromNode       = k1
          , toNode         = k2
          , edgeAttributes = [
              GV.Label (GV.StrLabel . T.pack . display $ pretty l)
            ]
          }

simplifySCC :: (IntDomain i, MemoryModel a) => MkJGraph i a -> MkJGraph i a
simplifySCC (MkJGraph gr ctx) = MkJGraph (Gr.delNodes (allnodes \\ sccnodes) gr) ctx
  where
    allnodes = Gr.nodes gr
    sccnodes = concat . filter (not . trivial) $ Gr.scc gr
    trivial [_] = True
    trivial _   = False

-- | Returns pairs of rewrite rules and constraints of a constructed
-- computation graph.
mkJGraph2TRS :: (Monad m, IntDomain i, MemoryModel a) => MkJGraph i a -> 
  JatM m (JGraph i a, [(Rule PAFun PAVar, [PATerm])])
{-mkJGraph2TRS (MkJGraph gr _) | trace ("gr" ++ show (Gr.nodes gr)) False = undefined-}
mkJGraph2TRS (MkJGraph gr _) = do
  p <- getProgram
  rs <- mapM (rule p) ledges
  return (gr,rs)
  where
    {-rule _ (k,k',_) | trace (show (k,k')) False = undefined-}
    rule _ (k,k',InstanceLabel) = ruleM (tsl s s k) (tsr s s k') []
      where s = lookupN k
    rule _ (k,k',RefinementLabel _) = ruleM (tsl t t k) (tsr t t k') []
      where t = lookupN k'
    rule p (k,k',EvaluationLabel con _) = 
      case maybePutField p s of
        Just q  -> ruleM (tsl s s k) (tsStar q s t k') (mkCon con)
        Nothing -> ruleM (tsl s s k) (tsr s t k') (mkCon con)
      where s = lookupN k
            t = lookupN k'

    ruleM ms mt con = do
      s <- ms
      t <- mt
      return (Rule {lhs = s, rhs = t}, con)
      
    lnodes = labNodes gr
    ledges = labEdges gr

    lookupN k = errmsg `fromMaybe` lookup k lnodes
    errmsg    = error "Jat.CompGraph.mkGraph2TRS: unexpected key"
    tsl       = state2TRS Nothing LHS
    tsr       = state2TRS Nothing RHS
    tsStar q  = state2TRS (Just q) RHS

    mkCon con = if isTop con then [] else [con]

-- Interactive
data Command = NSteps Int | Until Int | Run | Help | Exit deriving (Show, Read)


-- | Provides a simple prompt, allowing to analyze the construction of the
-- computation graph.
mkJGraphIO :: (IntDomain i, MemoryModel a) => P.ClassId -> P.MethodId -> JatM IO (MkJGraph i a)
mkJGraphIO cn mn = do
  liftIO $ putStrLn ":> enter command: (Help to see the list of commands)"
  mkInitialNode cn mn >>= mkJGraphPrompt

mkJGraphPrompt :: (IntDomain i, MemoryModel a) => MkJGraph i a -> JatM IO (MkJGraph i a)
mkJGraphPrompt mg@(MkJGraph _ []) = do
  liftIO $ writeFile "gr.dot" (dot2String $ mkJGraph2Dot mg)
  liftIO $ putStrLn "fin"
  return mg
mkJGraphPrompt mg@(MkJGraph g _) = do
  liftIO $ writeFile "gr.dot" (dot2String $ mkJGraph2Dot mg)
  liftIO $ print g
  liftIO $ putStr ">: "
  liftIO $ hFlush stdout
  ecmd <- liftIO parseCmd
  case ecmd of
    Left _    -> mkJGraphPrompt mg
    Right cmd -> case cmd of
      NSteps n -> mkNStepsIO n mg
      Until n  -> mkUStepsIO n mg
      Run      -> mkStepsIO mg
      Help     -> do
        liftIO $ putStrLn "NSteps int, Until pc, Run, Help, Exit"
        mkJGraphPrompt mg
      Exit -> return mg
  where 
    parseCmd = do
      cmd <- liftIO getLine
      E.try (E.evaluate (read cmd :: Command)) :: IO (Either E.SomeException Command)

mkNStepsIO :: (IntDomain i, MemoryModel a) => Int -> MkJGraph i a -> JatM IO (MkJGraph i a)
mkNStepsIO _ mg@(MkJGraph _ []) = mkJGraphPrompt mg
mkNStepsIO n mg | n < 1         = mkJGraphPrompt mg
mkNStepsIO n mg                 = mkStep mg >>= mkNStepsIO (n-1)

mkUStepsIO :: (IntDomain i, MemoryModel a) => Int -> MkJGraph i a -> JatM IO (MkJGraph i a)
mkUStepsIO _ _ = undefined

{-mkUStepsIO _ mg@(MkJGraph _ []) = mkJGraphPrompt mg-}
{-mkUStepsIO n mg | n ==  (pc .frm . state' . context mg) = mkJGraphPrompt mg-}
{-mkUStepsIO n mg                                          = mkStep mg >>= mkNStepsIO (n-1)-}

mkStepsIO :: (IntDomain i, MemoryModel a) => MkJGraph i a -> JatM IO (MkJGraph i a)
mkStepsIO mg@(MkJGraph _ []) = mkJGraphPrompt mg
mkStepsIO mg                 = mkStep mg >>= mkStepsIO

