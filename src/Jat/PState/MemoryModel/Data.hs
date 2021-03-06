-- | This module provides the interface for the memory model.
-- The memory model provides the (abstract) semantics for heap related
-- operations
module Jat.PState.MemoryModel.Data where

import Jat.Constraints (PATerm)
import Jat.JatM
import Jat.PState.AbstrValue
import Jat.PState.Data 
import Jat.PState.IntDomain 
import Jat.PState.Step
import Jat.Utils.Pretty (Pretty)
import qualified Jinja.Program as P


data Side = LHS | RHS
instance Show Side where
  show LHS = "l"
  show RHS = "r"

-- | Provides the interface for heap related operations.
class Pretty a => MemoryModel a where
  new       :: (Monad m, IntDomain i) => PState i a -> P.ClassId -> JatM m (PStep(PState i a))
  getField  :: (Monad m, IntDomain i) => PState i a -> P.ClassId -> P.FieldId -> JatM m (PStep(PState i a))
  putField  :: (Monad m, IntDomain i) => PState i a -> P.ClassId -> P.FieldId -> JatM m (PStep(PState i a))

  invoke    :: (Monad m, IntDomain i) => PState i a -> P.MethodId -> Int -> JatM m (PStep(PState i a))
  equals    :: (Monad m, IntDomain i) => PState i a -> JatM m (PStep(PState i a))
  nequals   :: (Monad m, IntDomain i) => PState i a -> JatM m (PStep(PState i a))

  initMem   :: (Monad m, IntDomain i) => P.ClassId -> P.MethodId -> JatM m (PState i a)

  leq       :: IntDomain i => P.Program -> PState i a -> PState i a -> Bool
  lub      :: (Monad m, IntDomain i) =>  PState i a -> PState i a -> JatM m (PState i a)
  widening  :: (Monad m, IntDomain i) =>  PState i a -> PState i a -> JatM m (PState i a)
  widening  = lub

  normalize :: PState i a -> PState i a
  -- TODO: refactor
  state2TRS :: (Monad m, IntDomain i) => Maybe Address -> Side -> PState i a -> PState i a -> Int -> JatM m PATerm

  update :: P.Program -> P.PC -> P.Instruction -> PState i a ->  PState i a
  update _ _ = const id

  preprocess :: P.Program -> P.PC -> P.Instruction -> PState i a ->  PState i a
  preprocess _ _ = const id

