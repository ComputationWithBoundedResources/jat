module JFlow.Flow where

import Jinja.Program

import JFlow.Data

import Data.List (find)
import Data.Array (Array)
import qualified Data.Array as A
import Control.Monad.State hiding (join)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Maybe (fromJust, fromMaybe)
{-import Debug.Trace-}
import qualified Text.PrettyPrint.ANSI.Leijen as P


-- Note : 
-- given context = (cn,mn,v) 
-- transition graph 1 : M:<main,x0> A:<A,a0> with M -> A
-- transition graph 2 : M:<main,x0> A:<A,a0> A':<A,a0'> with M -> A and M -> A'
-- suppose graph2 is obtained in some analysis eg class ; suppose graph 1 different analysis depending on former one
-- we would have to include a0/a0' into context; ie context does also depend on other transition graphs :(
-- either: former have to be joined - (querybase not enough anymore)
-- or: params have to be taken into account in the context ? we have a whole list of different values (dynamically)
--
-- whole context-sensitive analysis can be still obtained when considering product construction

data Context v = Context ClassId MethodId v deriving (Eq,Ord,Show)
type ContextMap v a = Map (Context v) a

newtype Facts v = Facts { unFacts :: Array Int v }
type FactBase v = ContextMap v (Facts v)

data CallString = Call ClassId MethodId PC CallString | Nil PC

queryCS :: Ord v => CallString -> Context v -> FactBase v -> QueryV v -> Query
queryCS (Nil pc)             ctx fb queryv = runQueryV (value ctx fb pc) queryv
queryCS (Call cn mn pc call) ctx fb queryv = queryCS call (Context cn mn (value ctx fb pc)) fb queryv

queryFrom :: Ord v => ClassId -> MethodId -> CallString -> FactBase v -> QueryV v -> Maybe Query
queryFrom cn fn cs fb q = find k (M.keys fb) >>= \ctx -> return (queryCS cs ctx fb q)
  where k (Context cn' fn' _) = cn' == cn && fn' == fn

instance Show v => Show (Facts v) where
  show (Facts fs) = show . P.list $ map (P.string . show) (A.assocs fs)

type Worklist = [PC]

entryPC :: PC
entryPC = 0


type AnnotatedContext v = (Context v, PC)
type Transition v       = (AnnotatedContext v, Context v)

data FlowState m v = FlowState {
    facts       :: FactBase v
  , worklist    :: Map (Context v) Worklist

  , callStack   :: [Context v]
  , transitions :: [Transition v]

  , program     :: Program
  }

type St m v a = State (FlowState m v) a

getsFacts :: Ord v => Context v -> St m v (Facts v)
getsFacts ctx = lookupx ctx `liftM` gets facts

getsFactsM :: Ord v => Context v -> St m v (Maybe (Facts v))
getsFactsM ctx = M.lookup ctx `liftM` gets facts

updateFact :: Ord v => Context v -> PC -> v -> St m v ()
updateFact ctx pc v = getsFacts ctx >>= \fs -> updateFacts ctx .  Facts $ unFacts fs A.// [(pc,v)]

updateFacts :: Ord v => Context v -> Facts v -> St m v ()
updateFacts ctx fs = modify (\st -> st{facts = M.insert ctx fs (facts st)})

lookupx :: Ord k => k -> Map k v -> v
lookupx k m = errmsg `fromMaybe` M.lookup k m
  where errmsg = error "assertion error: lookupx: key not found."

addTransition :: Transition v -> St m v ()
addTransition t = modify (\st -> st{transitions = t:transitions st})

pushCall :: Context v -> St m v ()
pushCall ctx = modify (\st -> st{callStack = ctx:callStack st})

pushCall' :: Eq v => Context v -> St m v ()
pushCall' ctx = modify (\st -> st{callStack = k (callStack st)})
  where k cs = if ctx `elem` cs then cs else cs ++ [ctx]

topCall :: St m v (Context v)
topCall = do
  xs <- gets callStack
  case xs of
    (c:_) -> return c
    []     -> error "assertion error: empty call stack"

popCall :: St m v (Context v)
popCall = do
  xs <- gets callStack
  case xs of
    (c:cs) -> modify (\st -> st{callStack=cs}) >> return c
    []     -> error "assertion error: empty call stack"

getsWorklist :: Ord v => Context v -> St m v Worklist
getsWorklist ctx = lookupx ctx `liftM` gets worklist

pushPC :: Ord v => Context v -> PC -> St m v ()
pushPC ctx pc = modify (\st -> st{worklist = M.insertWith (++) ctx [pc] (worklist st)})

pushPCs :: Ord v => Context v -> [PC] -> St m v ()
pushPCs ctx = mapM_ (pushPC ctx)

popPC :: Ord v => Context v -> St m v PC
popPC ctx = do
  xs <- M.lookup ctx `liftM` gets worklist
  case xs of
    Nothing -> error "assertion error: no worklist initialised"
    Just [] -> error "assertion error: empty worklist"
    Just (p:ps) -> modify (\st -> st{worklist = M.insert ctx ps (worklist st)}) >> return p

getsMethod :: ClassId -> MethodId -> St m v Method
getsMethod cn mn = gets program >>= \p -> return . snd $ seesMethodIn p cn mn

getsInstruction :: ClassId -> MethodId -> PC -> St m v Instruction
getsInstruction cn mn pc = do
  p <- gets program
  let (cn',_) = seesMethodIn p cn mn
  return $ instruction p cn' mn pc


value :: Ord v => Context v -> FactBase v -> PC -> v
value ctx fb pc = unFacts (lookupx ctx fb) A.! pc

------

analyse :: (Show v,Ord v) => Flow v -> Program -> ClassId -> MethodId -> (Facts v, FactBase v)
{-analyse _ _ _ _ | trace ">>> analyse" False = undefined-}
analyse flow p cn mn = evalState analyseM st0
  where
    analyseM = do
      let 
        val0 = setup (transfer flow) p cn mn
        ctx0 = Context cn mn val0
      setupContext flow ctx0
      analyseCallStack flow
      fb <- gets facts
      return (fromJust (M.lookup ctx0 fb), fb)
    st0 = mkInitState p

mkInitState :: Program -> FlowState m v
{-mkInitState _ | trace ">>> mkInitState" False = undefined-}
mkInitState p = FlowState {

    facts       = M.empty
  , worklist    = M.empty
  , callStack   = []
  , transitions = []

  , program     = p
}

setupContext :: (Show v, Ord v) => Flow v -> Context v -> St m v ()
{-setupContext _ ctx | trace (">>> setupContext" ++ show ctx) False = undefined-}
setupContext (Flow lat _ _) ctx@(Context cn mn v) = do
  md <- getsMethod cn mn
  let bottom  = bot lat
  updateFacts ctx (initFacts md bottom)
  updateFact ctx entryPC v
  pushPC ctx entryPC
  pushCall ctx
  where 
    initFacts md val = Facts $ A.listArray bounds (cycle [val])
      where bounds = A.bounds $ methodInstructions md

initContext :: (Show v, Ord v) => Flow v -> Context v -> St m v ()
{-initContext _ ctx | trace (">>> initContext" ++ show ctx) False = undefined-}
initContext (Flow lat tran quer) ctx@(Context cn mn v) = do
  md <- getsMethod cn mn
  p <- gets program
  let 
    bottom  = bot lat
    nparams = length $ methodParams md
    q       = runQueryV v quer
    val     = project tran p q cn mn nparams v
  updateFacts ctx (initFacts md bottom)
  updateFact ctx entryPC val
  pushPC ctx entryPC
  pushCall ctx
  where 
    initFacts md val = Facts $ A.listArray bounds (cycle [val])
      where bounds = A.bounds $ methodInstructions md

analyseCallStack :: (Show v, Ord v) => Flow v -> St m v ()
{-analyseCallStack flow = trace ">>> analyseCallStack" $ do-}
analyseCallStack flow = do
  stk <- gets callStack
  case stk of
    []      -> return ()
    (ctx:_) -> analyseContext flow ctx

analyseContext :: (Show v, Ord v) => Flow v -> Context v -> St m v ()
{-analyseContext flow ctx = trace ">>> analyseContext" $ do-}
analyseContext flow ctx = do
  wl  <- getsWorklist ctx
  if not $ null wl
    then popPC ctx >>= analyseInstruction flow ctx
    else do
      popCall
      callers <- filter ((==ctx) . snd) `liftM` gets transitions
      let callingCtxs = [(ctx',pc) | ((ctx',pc),_) <- callers]
      forM_ callingCtxs (uncurry pushPC)
      forM_ callingCtxs (pushCall' . fst)
      analyseCallStack flow
       
analyseInstruction :: (Show v,Ord v) => Flow v -> Context v -> PC -> St m v ()
{-analyseInstruction _ _ _ | trace ">>> analyseInstruction" False = undefined-}
analyseInstruction flow ctx@(Context cn mn _) pc = do
  ins <- getsInstruction cn mn pc
  newVal <- if isMethodCall ins
    then analyseCall' flow ctx ins pc
    else interpretInstruction flow ctx pc ins
  updateValue flow ctx pc ins newVal


analyseCall' :: (Show v, Ord v) => Flow v -> Context v -> Instruction -> PC -> St m v (Maybe v)
analyseCall' flow@(Flow lat tran quer)  ctx (Invoke mn n) pc = do
  p <- gets program
  fb <- gets facts
  let 
    val = value ctx fb pc
    q   = runQueryV val quer
    (lix,six) = hasIndexQ q
    ty  = hasTypeQ q (StkVar lix (six -n))
  case ty of 
    RefType cn -> do
      let
        subtys = subClassesOf p cn
        joinf            = join lat p
        processCall' fcn = processCall flow (ctx,pc) fcn mn val
      rvals <- mapM processCall' subtys
      {-let rvals' = map (reproject tran cn n) rvals-}
      {-let rval   = let r = foldl1 joinf rvals in trace ("RET:" ++ show (rvals,r)) r -}
      {-return . Just $ let r = extend tran p q cn n val rval in trace ("EXT:" ++ show (cn,n,val,rval,r)) r-}
      let rval   = foldl1 joinf rvals
      return . Just $ extend tran p q cn n val rval
    _ -> error "Flow.analyseCall': unexpected type"



updateValue :: (Show v, Ord v) => Flow v -> Context v -> PC -> Instruction -> Maybe v -> St m v ()
updateValue flow _ _ _ Nothing = analyseCallStack flow
updateValue flow@(Flow lat _ _) ctx pc ins (Just newVal) = do
  st <- get
  let
    joinf    = join lat (program st)
    fbase    = facts st
    vsuccs   = foldr (\spc -> let 
                                oldVal = value ctx fbase spc
                                {-joinVal = let r = newVal `joinf` oldVal in trace ("MRG:" ++ show (spc,oldVal,newVal,r)) r-}
                                joinVal = newVal `joinf` oldVal
                              in
                              if oldVal /= joinVal
                                 then ((spc,joinVal):)
                                 else id) [] (successors ins pc)
  {-mapM_ (\(lpc,v) -> trace (">update: " ++ show (lpc,v)) $ updateFact ctx lpc v) vsuccs-}
  mapM_ (uncurry $ updateFact ctx) vsuccs
  pushPCs ctx $ fst . unzip $ vsuccs
  analyseCallStack flow


interpretInstruction :: (Show v, Ord v) => Flow v -> Context v -> PC -> Instruction -> St m v (Maybe v)
{-interpretInstruction _ (Context cn mn _) pc ins | trace (">>> interpretInstruction " ++ show (cn,mn,pc,ins)) False = undefined-}
interpretInstruction (Flow _ tran quer) ctx pc ins = do
  st <- get
  let
    prog     = program st
    fbase    = facts st
    curVal   = value ctx fbase pc
  return . Just $ transf tran prog (runQueryV curVal quer) ins curVal

processCall :: (Show v, Ord v) => Flow v -> AnnotatedContext v -> ClassId -> MethodId -> v -> St m v v
{-processCall _ ctx cn mn v | trace (">>> processCall " ++ show (ctx,cn,mn,v)) False = undefined-}
processCall flow@(Flow lat _ _) callingCtx cn mn v = do
  let currentCtx = Context cn mn v
  addTransition (callingCtx, currentCtx)
  fsM <- getsFactsM currentCtx
  case fsM of
    Nothing -> initContext flow currentCtx >> return (bot lat)
    Just fs -> do
      p  <- gets program
      md <- getsMethod cn mn 
      let 
        returns = fst . unzip $ filter (isReturn . snd) (zip [0..] (A.elems $ methodInstructions md))
        values  = foldr (\i -> ((unFacts fs A.! i) :)) [] returns
        joinf   = join lat p
      return $ foldr1 joinf values





