module Jat.PState.Semantics where


import Jat.JatM
import Jat.PState.AbstrDomain
import Jat.PState.AbstrValue
import Jat.PState.BoolDomain
import Jat.PState.Data
import Jat.PState.Frame
import Jat.PState.IntDomain
import Jat.PState.MemoryModel
import Jat.PState.Step
import qualified Jat.Program as P

mkInitialState :: (Monad m, IntDomain i, MemoryModel a) => P.Program -> P.ClassId -> P.MethodId -> JatM m (PState i a)
mkInitialState = initMem

exec :: (Monad m, IntDomain i) => PState i a -> JatM m (PStep (PState i a))
exec st@(PState _ (Frame _ _ cn mn pc :_) _) = do
  p <- getProgram
  let ins = P.instruction p cn mn pc
  execInstruction p st ins
exec (PState _ [] _) = error "Jat.PState.Semantics.exec: empty stk."
exec (EState _)      = error "Jat.PState.Semantics.exec: exceptional state."

execInstruction :: (Monad m, IntDomain i) => P.Program -> PState i a -> P.Instruction -> JatM m (PStep (PState i a))
execInstruction p st@(PState _ _ _) ins = 
  case ins of
    -- frame operations
    P.Push v         -> execPush v    `applyF` st
    P.Pop            -> execPop       `applyF` st
    P.Load n         -> execLoad n    `applyF` st
    P.Store n        -> execStore n   `applyF` st
    P.Goto i         -> execGoto i    `applyF` st
    P.IfFalse n      -> execIfFalse n `applyF` st
    P.IAdd           -> execIAdd      `applyF` st
    P.ISub           -> execISub      `applyF` st
    P.BAnd           -> execBAnd      `applyF` st
    P.BOr            -> execBOr       `applyF` st
    P.CheckCast _    -> error "checkCast not implemented"
    P.BNot           -> execBNot    `applyF` st
    P.ICmpGeq        -> execICmpGeq `applyF` st
    P.CmpEq          -> execCmpEq   `applyF` st
    P.CmpNeq         -> execCmpNeq  `applyF` st
    -- inte frame operations
    P.Invoke mn n    -> error "not implemented yet"
    P.Return         -> execReturn st
    -- heap operations
    --P.New cn         -> execNew p s cn 
    --P.GetField fn cn -> execGetField p s cn fn
    --P.PutField fn cn -> execPutField p s cn fn
execInstruction _ (EState _) _ = error "Jat.PState.Semantics.exec: exceptional state."


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

execIfFalse :: Monad m => Int -> Frame i -> JatM m (PStep (Frame i))
execIfFalse i (Frame loc stk cn mn pc) = case stk of
  BoolVal b1:vs -> liftStep eval refine `liftM` ifFalse b1
    where
      eval   b = Frame loc vs cn mn (if b == constant True  then pc+1 else pc+i)
      refine b = Frame loc (BoolVal b:vs) cn mn pc
  _            -> error "Jat.PState.Semantics.execIfFalse: invalid stack."


execBinIntOp :: (Monad m, IntDomain i) => (i -> i -> JatM m (PStep i)) -> Frame i -> JatM m (PStep (Frame i))
execBinIntOp op (Frame loc stk cn mn pc) = case stk of
  IntVal i1: IntVal i2: vs -> liftPStep (\k -> Frame loc (IntVal k:vs) cn mn (pc+1)) `liftM` (i1 `op` i2)
  _ -> error "Jat.PState.Semantics.execBinIntOp: invalid stack."


execIAdd, execISub :: (Monad m, IntDomain i) => Frame i -> JatM m (PStep (Frame i))
execIAdd = execBinIntOp (+.)
execISub = execBinIntOp (-.)

execBinBoolOp :: Monad m => (BoolDomain -> BoolDomain -> JatM m (PStep BoolDomain)) -> Frame i -> JatM m (PStep (Frame i))
execBinBoolOp op (Frame loc stk cn mn pc) = case stk of
  BoolVal b1 :BoolVal b2 :vs -> liftPStep (\k -> Frame loc (BoolVal k:vs) cn mn (pc+1)) `liftM` (b1 `op` b2)
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

execCmpEq :: (Monad m, IntDomain i) => Frame i -> JatM m (PStep (Frame i))
execCmpEq fr@(Frame loc stk cn mn pc) = case stk of
  Null      :Null      :vs -> return . topEvaluation $ Frame loc ((BoolVal $ constant True) : vs) cn mn (pc+1)
  IntVal _  :IntVal _  :_  ->  execBinIntCmp (==.) fr
  BoolVal _ :BoolVal _ :_  ->  execBinBoolOp (.==.) fr
  Unit      :Unit      :_  ->  error "Jat.PState.Semantics.execCmpEq : illegal unit access."
  _ -> error "Jat.PState.Semantics.execcmpEq: heap not implemented yet"

execCmpNeq :: (Monad m, IntDomain i) => Frame i -> JatM m (PStep (Frame i))
execCmpNeq fr@(Frame loc stk cn mn pc) = case stk of
  Null      :Null      :vs -> return . topEvaluation $ Frame loc ((BoolVal $ constant False) : vs) cn mn (pc+1)
  IntVal _  :IntVal _  :_  ->  execBinIntCmp (==.) fr
  BoolVal _ :BoolVal _ :_  ->  execBinBoolOp (.==.) fr
  Unit      :Unit      :_  ->  error "Jat.PState.Semantics.execCmpEq : illegal unit access."
  _ -> error "Jat.PState.Semantics.execCmpEq: heap not implemented yet"

-- inter frame operations
execReturn :: (Monad m) => PState i a -> JatM m (PStep (PState i a))
execReturn (PState hp [_] ann) = return . topEvaluation $ PState hp [] ann
execReturn (PState hp (Frame _ (val:_) _ _ _ :Frame loc2 stk2 cn2 mn2 pc2 :frms) ann) =
  return . topEvaluation $ PState hp (Frame loc2 (val:stk2) cn2 mn2 (pc2+1):frms) ann
execReturn (PState _ _ _) = error "Jat.PState.Semantcs.execReturn: illegal stack."
execReturn (EState _)     = error "Jat.PState.Semantics.execRetur: exceptional state."
