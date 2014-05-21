-- | This module implements the (abstract) semantics of JBC instructions.
-- Heap related operations are delegated to the 'MemoryModel'.
module Jat.PState.Semantics 
  (
    mkInitialState
  , exec
  )
where


import Jat.JatM
import Jat.PState.AbstrDomain as AD
import Jat.PState.AbstrValue
import Jat.PState.BoolDomain
import Jat.PState.Data
import Jat.PState.Frame
import Jat.PState.IntDomain
import Jat.PState.MemoryModel
import Jat.Utils.Pretty (pretty)
import Jat.PState.Step
import qualified Jinja.Program as P

--import Jat.Utils.Pretty hiding (equals)
import Debug.Trace

-- | Constructs the initial state for a given class name and method name.
mkInitialState :: (Monad m, IntDomain i, MemoryModel a) => P.ClassId -> P.MethodId -> JatM m (PState i a)
mkInitialState = initMem

-- | Performs a single step.
exec :: (Monad m, IntDomain i, MemoryModel a) => PState i a -> JatM m (PStep (PState i a))
exec st@(PState _ (Frame _ _ cn mn pc :_) _) = do
  p <- getProgram
  let ins = P.instruction p cn mn pc
  st2 <- execInstruction st pc (trace (">>> exec: " ++ show ins) ins)
  return $ trace ("<<< exec" ++ show (liftPStep (show . pretty) st2)) st2
  execInstruction st pc ins
  
exec (PState _ [] _) = error "Jat.PState.Semantics.exec: empty stk."
exec (EState _)      = error "Jat.PState.Semantics.exec: exceptional state."

execInstruction :: (Monad m, IntDomain i, MemoryModel a) => PState i a -> P.PC -> P.Instruction -> JatM m (PStep (PState i a))
execInstruction st@(PState{}) pc ins = do
  p <- getProgram
  step <- case ins of
    -- frame operations
    P.Push v         -> execPush v    `applyF` st
    P.Pop            -> execPop       `applyF` st
    P.Load n         -> execLoad n    `applyF` st
    P.Store n        -> liftPStep normalize `liftM` (execStore n `applyF` st)
    P.Goto i         -> execGoto i    `applyF` st
    P.IfFalse n      -> execIfFalse n `applyF` st
    P.IAdd           -> execIAdd      `applyF` st
    P.ISub           -> execISub      `applyF` st
    P.BAnd           -> execBAnd      `applyF` st
    P.BOr            -> execBOr       `applyF` st
    P.CheckCast _    -> error "checkCast not implemented"
    P.BNot           -> execBNot    `applyF` st
    P.ICmpGeq        -> execICmpGeq `applyF` st
    -- inter frame operations
    P.Return         -> execReturn st
    P.Invoke mn n    -> execInvoke st mn n
    -- heap operations
    P.CmpEq          -> execCmpEq st
    P.CmpNeq         -> execCmpNeq st
    P.New cn         -> execNew st cn 
    P.GetField fn cn -> execGetField st cn fn
    P.PutField fn cn -> execPutField st cn fn
  return $ case step of
    Evaluation (st2,con) -> Evaluation (update p pc ins st2, con)
    s                    -> s
execInstruction (EState _) _ _ = error "Jat.PState.Semantics.exec: exceptional state."


-- frame operations
applyF :: Monad m => (Frame i -> JatM m (PStep (Frame i))) -> PState i a -> JatM m (PStep (PState i a))
applyF execf (PState hp (frm:frms) ann) = do
  frm' <- execf frm
  return $ (\lfrm -> PState hp (lfrm:frms) ann) `liftPStep` frm' 
applyF _ (PState _ [] _) = error "Jat.PState.Semantics.applyF: empty stack."
applyF _ (EState _)      = error "Jat.PState.Semantics.applyF: exceptional state."

execPush :: (Monad m, IntDomain i) => P.Value -> Frame i -> JatM m (PStep (Frame i))
execPush val (Frame loc stk cn mn pc) = return $ topEvaluation (Frame loc (aval:stk) cn mn (pc+1))
  where aval = abstract val

execPop :: Monad m => Frame i -> JatM m (PStep (Frame i))
execPop (Frame loc stk cn mn pc) = case stk of 
  _:vs -> return $ topEvaluation (Frame loc vs cn mn (pc+1))
  _    -> error "Jat.PState.Semantics.execPop: empty stack."

execLoad :: (Monad m, IntDomain i) => Int -> Frame i -> JatM m (PStep (Frame i))
execLoad n (Frame loc stk cn mn pc) = return $ topEvaluation (Frame loc (v:stk) cn mn (pc+1))
  where v = n `lookupL` loc

execStore :: (Monad m, IntDomain i) => Int -> Frame i -> JatM m (PStep (Frame i))
execStore n (Frame loc stk cn mn pc) = case stk of
  v:vs -> return $ topEvaluation (Frame loc' vs cn mn (pc+1))
    where loc' = updateL n v loc
  _ -> error "Jat.PState.Semantics.execStore: invalid stack."

execGoto :: Monad m => Int -> Frame i -> JatM m (PStep (Frame i))
execGoto i (Frame loc stk cn mn pc) = return $ topEvaluation (Frame loc stk cn mn (pc+i))

-- TODO: 
-- refinement should be substituted in whole state;
-- in generic case not helpful ie Load 1; Load 2: BOr; IfFalse
-- special case Load 1; IfFalse
execIfFalse :: Monad m => Int -> Frame i -> JatM m (PStep (Frame i))
execIfFalse i frm@(Frame loc stk cn mn pc) = case stk of
  BoolVal b1:vs -> do
    eva <- ifFalse b1
    return $ case eva of
      Evaluation (b,c) -> topEvaluation $ Frame loc vs cn mn (pc + if b == constant True  then 1 else i)
      Refinement rs    -> Refinement $ map (\(r,c) -> (mapValuesF (k r) frm, c)) rs
      where
        k r (BoolVal b) = BoolVal $ r b
        k r v           = v
  _            -> error "Jat.PState.Semantics.execIfFalse: invalid stack."
  {-BoolVal b1:vs -> liftStep eval refine `liftM` ifFalse b1-}
    {-where-}
      {-eval   b = Frame loc vs cn mn (pc + if b == constant True  then 1 else i)-}
      {-refine b = Frame loc (BoolVal (b b1):vs) cn mn pc-}


execBinIntOp :: (Monad m, IntDomain i) => (i -> i -> JatM m (PStep i)) -> Frame i -> JatM m (PStep (Frame i))
execBinIntOp op (Frame loc stk cn mn pc) = case stk of
  IntVal i1: IntVal i2: vs -> liftPStep (\k -> Frame loc (IntVal k:vs) cn mn (pc+1)) `liftM` (i2 `op` i1)
  _ -> error "Jat.PState.Semantics.execBinIntOp: invalid stack."


execIAdd, execISub :: (Monad m, IntDomain i) => Frame i -> JatM m (PStep (Frame i))
execIAdd = execBinIntOp (+.)
execISub = execBinIntOp (-.)

execBinBoolOp :: Monad m => (BoolDomain -> BoolDomain -> JatM m (PStep BoolDomain)) -> Frame i -> JatM m (PStep (Frame i))
execBinBoolOp op (Frame loc stk cn mn pc) = case stk of
  BoolVal b1 :BoolVal b2 :vs -> liftPStep (\k -> Frame loc (BoolVal k:vs) cn mn (pc+1)) `liftM` (b2 `op` b1)
  _ -> error "Jat.PState.Semantics.execBinIntOp: invalid stack."

execBAnd, execBOr :: Monad m => Frame i -> JatM m (PStep (Frame i))
execBAnd = execBinBoolOp (.&&.)
execBOr  = execBinBoolOp (.||.)

execBNot :: Monad m => Frame i -> JatM m (PStep (Frame i))
execBNot (Frame loc stk cn mn pc) = case stk of
  BoolVal b :vs -> liftPStep (\notb -> Frame loc (BoolVal notb :vs) cn mn (pc+1)) `liftM` (.!) b
  _ -> error "Jat.PState.Semantics.execBNot: invalid stack."
 
execBinIntCmp :: (Monad m, IntDomain i) => (i -> i -> JatM m (Step BoolDomain i)) -> Frame i -> JatM m (PStep (Frame i))
execBinIntCmp cmp (Frame loc stk cn mn pc) = case stk of
  IntVal i1 :IntVal i2 :vs -> liftStep eval refine  `liftM` (i2 `cmp` i1)
    where
      eval   b = Frame loc (BoolVal b :vs) cn mn (pc+1)
      refine k = Frame loc (IntVal k :vs) cn mn pc
  _ -> error "Jat.PState.Semantics.execBinIntOp: invalid stack."

execICmpGeq :: (Monad m, IntDomain i) => Frame i -> JatM m (PStep (Frame i))
execICmpGeq = execBinIntCmp (>=.)

execCmpEq :: (Monad m, IntDomain i,MemoryModel a) => PState i a -> JatM m (PStep (PState i a))
execCmpEq st@(PState hp (Frame loc stk cn mn pc:frms) ann) = case stk of
  Null      :Null      :vs -> return . topEvaluation $ PState hp (Frame loc ((BoolVal $ constant True) : vs) cn mn (pc+1):frms) ann
  IntVal _  :IntVal _  :_  ->  execBinIntCmp (==.) `applyF` st
  BoolVal _ :BoolVal _ :_  ->  execBinBoolOp (.==.) `applyF` st
  Unit      :Unit      :_  ->  error "Jat.PState.Semantics.execCmpEq : illegal unit access."
  _ -> equals st
execCmpEq _ = error "Jat.PState.Semantics.execCmpEq: unexpected case."

execCmpNeq :: (Monad m, IntDomain i,MemoryModel a) => PState i a -> JatM m (PStep (PState i a))
execCmpNeq st@(PState hp (Frame loc stk cn mn pc:frms) ann) = case stk of
  Null      :Null      :vs -> return . topEvaluation $ PState hp (Frame loc ((BoolVal $ constant False) : vs) cn mn (pc+1):frms) ann
  IntVal _  :IntVal _  :_  ->  execBinIntCmp (/=.) `applyF` st
  BoolVal _ :BoolVal _ :_  ->  execBinBoolOp (./=.) `applyF` st
  Unit      :Unit      :_  ->  error "Jat.PState.Semantics.execCmpEq : illegal unit access."
  _ -> nequals st
execCmpNeq _ = error "Jat.PState.Semantics.execCmpEq: unexpected case."

-- inter frame operations
execReturn :: (Monad m) => PState i a -> JatM m (PStep (PState i a))
execReturn (PState hp [_] ann) = return . topEvaluation $ PState hp [] ann
execReturn (PState hp (Frame _ (val:_) _ _ _ :Frame loc2 stk2 cn2 mn2 pc2 :frms) ann) =
  return . topEvaluation $ PState hp (Frame loc2 (val:stk2) cn2 mn2 (pc2+1):frms) ann
execReturn (PState{}) = error "Jat.PState.Semantcs.execReturn: illegal stack."
execReturn (EState _)     = error "Jat.PState.Semantics.execReturN: exceptional state."

execInvoke :: (Monad m, IntDomain i, MemoryModel a) => PState i a -> P.MethodId -> Int -> JatM m (PStep (PState i a))
execInvoke = invoke

-- heap operations

execNew :: (Monad m, IntDomain i, MemoryModel a) => PState i a -> P.ClassId -> JatM m (PStep (PState i a))
execNew = new

execGetField :: (Monad m, IntDomain i, MemoryModel a) => PState i a -> P.ClassId -> P.FieldId -> JatM m (PStep (PState i a))
execGetField (PState hp (Frame loc (_:stk) fcn mn pc: frms) ann) _ (P.FieldId "randI") = do
  rand <- IntVal `liftM` (constant 0 `AD.join` constant 666)
  return . topEvaluation $ PState hp (Frame loc (rand:stk) fcn mn (pc+1):frms) ann
execGetField (PState hp (Frame loc (_:stk) fcn mn pc: frms) ann) _ (P.FieldId "randB") = do
  rand <- BoolVal `liftM` (constant True `AD.join` constant False)
  return . topEvaluation $ PState hp (Frame loc (rand:stk) fcn mn (pc+1):frms) ann
execGetField st cn fn = getField st cn fn

execPutField :: (Monad m, IntDomain i, MemoryModel a) => PState i a -> P.ClassId -> P.FieldId -> JatM m (PStep (PState i a))
execPutField = putField 



