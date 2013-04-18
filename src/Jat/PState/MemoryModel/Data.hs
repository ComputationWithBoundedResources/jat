-- | This module provides the interface for the memory model.
-- The memory model provides the (abstract) semantics for heap related
-- operations
module Jat.PState.MemoryModel.Data where

import Jat.JatM
import Jat.PState.AbstrValue
import Jat.PState.Data 
import Jat.PState.IntDomain 
import Jat.PState.Step
import Jat.Utils.Pretty (Pretty)
import qualified Jat.Program as P

import qualified Data.Rewriting.Term as TRS (Term (..)) 

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
  join      :: (Monad m, IntDomain i) =>  PState i a -> PState i a -> JatM m (PState i a)
  widening  :: (Monad m, IntDomain i) =>  PState i a -> PState i a -> JatM m (PState i a)
  widening  = join

  normalize :: PState i a -> PState i a
  state2TRS :: (Monad m, IntDomain i) => Maybe Address -> PState i a -> Int -> JatM m (TRS.Term String String)

