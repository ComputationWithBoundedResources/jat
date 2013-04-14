{-# LANGUAGE BangPatterns #-}
module Jat.CompGraph 
  (
    MkJGraph
  , mkJGraph
  , mkJGraph2Dot
  , mkJGraph2TRS
  , mkJGraphIO
  )
where


import Jat.JatM
import Jat.PState
import qualified Jat.Program as P
import Jat.Utils.Pretty
import Jat.Utils.Dot
import Jat.Utils.Fun
import Jat.Constraints
import Data.Rewriting.Rule (Rule (..))
import qualified Data.Rewriting.Constraint as RC

import System.IO (hFlush,stdout)
import Control.Monad.State hiding (join)
import Data.Graph.Inductive as Gr
import Data.GraphViz.Types.Canonical
import qualified Control.Exception as E
import qualified Data.GraphViz.Attributes.Complete as GV
import qualified Data.Text.Lazy as T
import Data.Maybe (fromMaybe)


import Debug.Trace


-- finding instance/merge nodes for backjumps
-- assumptions: 
-- * code is unstructured, i.e. decomposition in general not possible
-- * if there are multiple candidates then one is the predecessor of the other one
--   i.e. c1 ->n -> c2 ->n e is valid but c1 ->n e, c2 ->n e, c1 /->n c2, c2 /-> c1 not
--   then predecessor is defined by wrt. to the transivity relation
-- finding a candidate reduces to (predc) topsort if we do not allow merging of nodes stemming from different back jump points

data ELabel     = EvaluationLabel Constraint | InstanceLabel | RefinementLabel Constraint deriving Show
instance Pretty ELabel where
  pretty (EvaluationLabel fm) = pretty fm
  pretty (RefinementLabel fm) = pretty fm
  pretty l                    = text $ show l
type NLabel i a = PState i a

type JGraph i a   = Gr (NLabel i a) ELabel
type JContext i a = Context (NLabel i a) ELabel
-- 'MkJGraph' consists of a Graph and a list of Contexts ('JContext'). A Context
-- corresponds to a (non-terminal) leaf node.
data MkJGraph i a  = MkJGraph (JGraph i a) [JContext i a]

mkJGraph :: (Monad m, IntDomain i, MemoryModel a) => P.ClassId -> P.MethodId -> JatM m (MkJGraph i a) 
mkJGraph cn mn = mkInitialNode cn mn >>= mkSteps

mkInitialNode :: (Monad m, IntDomain i, MemoryModel a) => P.ClassId -> P.MethodId -> JatM m (MkJGraph i a)
mkInitialNode cn mn = do
  k <- freshKey
  st <- mkInitialState cn mn
  let ctx = ([],k,st,[]) 
      g   = ctx & Gr.empty
  return $ MkJGraph g [ctx]


state' :: JContext i a -> PState i a
state' = lab'

isTerminal' :: JContext i a -> Bool
isTerminal' (_,_,st,s) = null s && isTerminal st

--isBackJump' :: Monad m => JContext i a -> JatM m Bool
--isBackJump' = isBackJump . state'

isTarget' :: Monad m => JContext i a -> JatM m Bool
isTarget' = isTarget . state'

isSimilar' :: JContext i a -> JContext i a -> Bool
isSimilar' ctx1 ctx2 = isSimilar (state' ctx1) (state' ctx2)

leq' :: (Monad m, IntDomain i, MemoryModel a) => JContext i a -> JContext i a -> JatM m Bool
leq' ctx1 ctx2 = getProgram >>= \p -> return $ leq p (state' ctx1) (state' ctx2)

join' :: (Monad m, IntDomain i, MemoryModel a) => JContext i a -> JContext i a -> JatM m (PState i a)
join' ctx1 ctx2 = join (state' ctx1) (state' ctx2)

mkSteps :: (Monad m, IntDomain i, MemoryModel a) => MkJGraph i a -> JatM m (MkJGraph i a)
mkSteps mg@(MkJGraph _ [])                        = return mg
mkSteps mg                                        = mkStep mg >>= mkSteps

mkStep :: (Monad m, IntDomain i, MemoryModel a) => MkJGraph i a -> JatM m (MkJGraph i a) 
mkStep (MkJGraph g (ctx:ctxs)) | isTerminal' ctx = return $ MkJGraph g ctxs
mkStep g                                         = tryLoop g |>> mkEval g


-- FIXME:
-- use target rather than backjump
-- exclude nod itself
tryLoop :: (Monad m, IntDomain i, MemoryModel a) => MkJGraph i a -> JatM m (Maybe (MkJGraph i a))
tryLoop (MkJGraph _ [])                              = error "Jat.CompGraph.tryInstance: empty context."
tryLoop mg@(MkJGraph g (ctx:_))                      = do
  b <- isTarget' ctx
  if b then eval candidates else return Nothing
  where
    eval ns | null ns = return Nothing
    eval ns           = Just `liftM` (tryInstance nctx mg |>> (mkJoin nctx mg >>= mkEval))
      where nctx = head ns
    candidates = [ n | Just n <- bfsnWith (condition ctx) (pre' ctx) (grev g)]
    --candidates = do
      --Just n <-  bfsnWith (\lctx -> trace (show (ctx,lctx) ++ show (condition ctx lctx)) condition ctx lctx) (suc g $ node' ctx) (grev g)
      --return n
    condition ctx1 ctx2 =
      if isSimilar' ctx1 ctx2 && null [ undefined | (_,_,RefinementLabel _) <- inn' ctx2] then Just ctx2 else Nothing


tryInstance :: (Monad m, IntDomain i, MemoryModel a) => JContext i a -> MkJGraph i a -> JatM m (Maybe (MkJGraph i a))
tryInstance ctx2 (MkJGraph _ (ctx1:_)) | trace (">>> tryInstance: " ++ show (ctx2,ctx1)) False = undefined
tryInstance ctx2 mg@(MkJGraph _ (ctx1:_)) = do
  b <- leq' ctx1 ctx2
  if trace("isInstance: " ++ show b) b then Just `liftM` mkInstanceNode ctx2 mg else return Nothing
tryInstance _ _ = return Nothing

mkInstanceNode :: Monad m => JContext i a -> MkJGraph i a -> JatM m (MkJGraph i a)
mkInstanceNode ctx2 (MkJGraph g (ctx1:ctxs)) = return $ MkJGraph g' ctxs
  where g' = insEdge (node' ctx1, node' ctx2, InstanceLabel) g
mkInstanceNode _ _ = error "Jat.CompGraph.mkInstance: empty context."


mkJoin :: (Monad m, IntDomain i, MemoryModel a) => JContext i a -> MkJGraph i a -> JatM m (MkJGraph i a)
mkJoin ctx2 (MkJGraph _ (ctx1:_)) | trace (">>> mkJoin: \n" ++ show (ctx2,ctx1)) False = undefined
mkJoin ctx2 (MkJGraph g (ctx1:ctxs)) = do
  k   <- freshKey
  st3 <- join' ctx1 (trace (show ctx2) ctx2)
  let edge = (InstanceLabel, node' ctx2)
      ctx3 = trace ("join: \n" ++ show st3) ([edge],k,st3,[])
      !g1  = delNodes successors g
      !g2   = ctx3 & g1
  return $ MkJGraph g2 (ctx3: filter (\lctx -> node' lctx `notElem` successors) ctxs)
  {-return $ MkJGraph g2 (ctx3: ctxs)-}
  where  successors = filter (/= node' ctx2) $ dfs [node' ctx2] g
mkJoin _ _ = error "Jat.CompGraph.mkInstance: empty context."

mkEval :: (Monad m, IntDomain i, MemoryModel a) => MkJGraph i a -> JatM m (MkJGraph i a)
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
      addNode k1 (MkJGraph g1 ctxs1) (st,cons) = do
          k2 <- freshKey
          let edge = (label cons, k1)
              ctx2 = ([edge],k2,st,[])
              g2   = ctx2 & g1
          return $ MkJGraph g2 (ctx2:ctxs1)
    addNodes _ _ _ = error "Jat.CompGraph.mkEval: assertion error: unexpected case."

mkEval _ = error "Jat.CompGraph.mkEval: emtpy context."

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
          GV.Label (GV.StrLabel . T.pack . display $ text "s" <> int k <$> pretty st)
        , GV.Shape GV.BoxShape
        ]
      }
    mkCtxNode (k,st) = 
      DotNode {
        nodeID = -k
      , nodeAttributes = [
          GV.Label (GV.StrLabel . T.pack . display $ text "s" <> int k <$> pretty st)
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

mkJGraph2TRS :: (Monad m, IntDomain i, MemoryModel a) => MkJGraph i a -> JatM m [Rule String String]
mkJGraph2TRS (MkJGraph g _) = getProgram >>= \p -> reverse `liftM` mapM (rule p) ledges
  where
    rule _ (k,k',InstanceLabel) = ruleM (ts s k) (ts s k') Nothing
      where s = lookupN k
    rule _ (k,k',RefinementLabel cons) = ruleM (ts t k) (ts t k') (Just $ translateConstraint cons)
      where t = lookupN k'
    rule p (k,k',EvaluationLabel cons) = 
      case maybePutField p s of
        Just q  -> ruleM (ts s k) (tsStar q t k') (Just $ translateConstraint cons)
        Nothing -> ruleM (ts s k) (ts t k') (Just $ translateConstraint cons)
      where s = lookupN k
            t = lookupN k'

    ruleM ms mt cons = do
      s <- ms
      t <- mt
      return Rule {lhs = s, rhs = t, con = cons}
      
    lnodes = labNodes g
    ledges = labEdges g

    lookupN k = errmsg `fromMaybe` lookup k lnodes
    errmsg    = error "Jat.CompGraph.mkGraph2TRS: unexpected key"
    ts        = state2TRS Nothing
    tsStar q  = state2TRS (Just q)

  
    -- refactor
    translateConstraint :: Constraint -> RC.Constraint String 
    translateConstraint cons = case cons of
      CVar i  -> RC.Atom $ RC.V i
      IConst i -> RC.Atom $ RC.I i
      BConst b -> RC.Atom $ if b then RC.Top else RC.Bot

      Not c     -> RC.Not (tc c)
      And c1 c2 -> RC.And (tc c1) (tc c2)
      Or  c1 c2 -> RC.Or (tc c1) (tc c2)

      Ass c1 c2 -> RC.Ass (tc c1) (tc c2)
      Eq  c1 c2 -> RC.Eq (tc c1) (tc c2)
      Neq c1 c2 -> RC.Neq (tc c1) (tc c2)
      Gte c1 c2 -> RC.Gte (tc c1) (tc c2)

      Add c1 c2 -> RC.Add (tc c1) (tc c2)
      Sub c1 c2 -> RC.Sub (tc c1) (tc c2)
      where tc = translateConstraint

-- Interactive
data Command = NSteps Int | Until Int | Run | Help | Exit deriving (Show, Read)


mkJGraphIO :: (IntDomain i, MemoryModel a) => P.ClassId -> P.MethodId -> JatM IO (MkJGraph i a)
mkJGraphIO cn mn = do
  liftIO $ putStrLn ":> enter command: (help to see the list of commands)"
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

