module Jat.PState.MemoryModel.Primitive 
  (
  Primitive
  )
where

import Jat.JatM
import Jat.PState.Data
import Jat.PState.AbstrValue
import qualified Jat.PState.AbstrDomain as AD
import Jat.PState.Heap
import Jat.PState.Frame
import Jat.PState.Fun
import Jat.PState.IntDomain
import Jat.PState.MemoryModel.Data
import Jat.Utils.Pretty
import qualified Jat.Program as P

import Control.Monad (zipWithM)

data Primitive = Primitive deriving Show
instance Pretty Primitive where pretty _ = text ""

instance MemoryModel Primitive where
  new       = error "Jat.PState.MemoryModel.Primitive: not supported."
  getField  = error "Jat.PState.MemoryModel.Primitive: not supported."
  putField  = error "Jat.PState.MemoryModel.Primitive: not supported."

  invoke    = error "Jat.PState.MemoryModel.Primitive: not supported."
  equals    = error "Jat.PState.MemoryModel.Primitive: not supported."
  nequals   = error "Jat.PState.MemoryModel.Primitive: not supported."

  initMem   = initMemx

  leq       = leqx
  join      = joinx

  state2TRS = undefined
 
initMemx :: (Monad m, IntDomain i) => P.ClassId -> P.MethodId -> JatM m (PState i Primitive)
initMemx cn mn = do
  p <- getProgram
  let m   = P.theMethod p cn mn
  params <- mapM defaultAbstrValue $ P.methodParams m 
  let loc = initL params $ P.maxLoc m
  return $ PState emptyH [Frame loc [] cn mn 0] Primitive
  where 
    defaultAbstrValue P.BoolType = BoolVal `liftM` AD.top
    defaultAbstrValue P.IntType  = IntVal `liftM` AD.top
    defaultAbstrValue P.NullType = return Null
    defaultAbstrValue P.Void     = return Unit
    defaultAbstrValue _          = error "Jat.PState.MemorModel.Primitive: not supported"

leqx :: IntDomain i => P.Program -> PState i Primitive -> PState i Primitive -> Bool
leqx _ st1 st2 | not (isSimilar st1 st2) = error "Jat.PState.MemoryModel.NoMem: unexpected case."
leqx _ st1 st2 = frames st1 `leqFS` frames st2
  where
    frms1 `leqFS` frms2 = and $ zipWith leqF frms1 frms2
    frm1  `leqF`  frm2  = and $ zipWith leqV (elemsF frm1) (elemsF frm2)

    Unit       `leqV` _          = True
    Null       `leqV` Null       = True
    BoolVal b1 `leqV` BoolVal b2 = b1 `AD.leq` b2
    IntVal i1  `leqV` IntVal i2  = i1 `AD.leq` i2
    _          `leqV` _          = error "Jat.PState.MemoryModel.Primitive: not supported."

joinx :: (Monad m, IntDomain i) => PState i Primitive -> PState i Primitive -> JatM m (PState i Primitive)
joinx st1 st2 = do
  frms3 <- frames st1 `joinFS` frames st2
  return $ PState (heap st1) frms3 Primitive
  where
    frms1 `joinFS` frms2 = zipWithM joinF frms1 frms2
    Frame loc1 stk1 cn1 mn1 pc1  `joinF`  Frame loc2 stk2 _ _ _  = do
      loc3 <- zipWithM joinV (elemsL loc1) (elemsL loc2)
      stk3 <- zipWithM joinV (elemsL stk1) (elemsL stk2)
      return $ Frame loc3 stk3 cn1 mn1 pc1

    Unit       `joinV` v          = return v
    Null       `joinV` Null       = return Null
    BoolVal b1 `joinV` BoolVal b2 = BoolVal `liftM` (b1 `AD.join` b2)
    IntVal i1  `joinV` IntVal i2  = IntVal  `liftM` (i1 `AD.join` i2)
    _          `joinV` _          = error "Jat.PState.MemoryModel.Primitive: not supported."


