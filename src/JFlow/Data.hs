{-# LANGUAGE TypeOperators #-}
module JFlow.Data where

import Jat.Utils.Pretty

import Jinja.Program as P
import Jinja.Program.Data ()

-- callstring
data Call       = Call ClassId MethodId deriving (Eq,Ord)
data CallSite   = CallSite ClassId MethodId PC deriving (Eq,Ord)
data CallString = CallString Call [CallSite] deriving (Eq,Ord,Show)

instance Show Call where
  show (Call cn (MethodId mn)) = show $ pretty cn <> char '.' <> string mn

instance Show CallSite where
  show (CallSite cn (MethodId mn) pc) = show $ pretty cn <> char '.' <> string mn <> char '.' <> int pc


data SemiLattice v = SemiLattice
  { name  :: String
  , bot   :: v
  , merge :: P.Program -> v -> v -> v }

data Transfer v w = Transfer
  { transf  :: P.Program -> (CallString,PC) -> P.Instruction -> (w,w) -> v -> v
  , setup   :: P.Program -> P.ClassId -> P.MethodId -> v
  , project :: P.Program -> P.ClassId -> P.MethodId -> Int -> w -> v -> v
  , extend  :: P.Program -> P.ClassId -> Int -> w -> v -> v -> v }

data Flow v w = Flow
  { lattice  :: SemiLattice v
  , transfer :: Transfer v w }


-- queries

class HasIndexQ w        where hasIndexQ        :: w -> (Int, Int)
class HasTypeQ w         where hasTypeQ         :: w -> Var -> P.Type

class MayShareQ w        where mayShareQ        :: w -> Var -> Var -> Bool
class MaySharesWithQ w   where maySharesWithQ   :: w -> Var -> [Var]
class MaySharingVarsQ w  where maySharingVarsQ  :: w -> [(Var,Var)]

class MayReachQ w        where mayReachQ        :: w -> Var -> Var -> Bool
class MayReachesQ w      where mayReachesQ      :: w -> Var -> [Var]
class MayReachingVarsQ w where mayReachingVarsQ :: w -> [(Var,Var)]
class IsAcyclicQ w       where isAcyclicQ       :: w -> Var -> Bool
class AcyclicVarsQ w     where acyclicVarsQ     :: w -> [Var]

class MayAliasQ w        where mayAliasQ        :: w -> Var -> Var -> Bool

