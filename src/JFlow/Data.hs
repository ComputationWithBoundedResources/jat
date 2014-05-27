{-# LANGUAGE TypeOperators #-}
{-[># LANGUAGE MultiParamTypeClasses #<]-}
{-[># LANGUAGE FlexibleInstances #<]-}
{-[># LANGUAGE UndecidableInstances #<]-}

module JFlow.Data where

import Jinja.Program as P

import Text.PrettyPrint.ANSI.Leijen
import Control.Monad (mplus)
import Data.Maybe (fromMaybe)

{-import Debug.Trace-}

-- FIXME: for some reason instance are not available

instance Pretty Var where
  pretty (LocVar i j) = char 'l' <> int i <> int j
  pretty (StkVar i j) = char 's' <> int i <> int j

instance Pretty Type where
  pretty BoolType     = text "bool"
  pretty IntType      = text "int"
  pretty (RefType cn) = pretty cn
  pretty (NullType)   = text "NT"
  pretty Void         = text "void"

instance Pretty ClassId where
  pretty (ClassId cn) = string cn

-- callstring
data Call       = Call ClassId MethodId deriving (Eq,Ord)
data CallSite   = CallSite ClassId MethodId PC deriving (Eq,Ord)
data CallString = CallString Call [CallSite] deriving (Eq,Ord,Show)

instance Show Call where
  show (Call cn (MethodId mn)) = show $ pretty cn <> char '.' <> string mn

instance Show CallSite where
  show (CallSite cn (MethodId mn) pc) = show $ pretty cn <> char '.' <> string mn <> char '.' <> int pc


data SemiLattice v = SemiLattice {
    name :: String
  , bot  :: v
  , join :: P.Program -> v -> v -> v
}

data Transfer v w = Transfer {
      transf  :: P.Program -> (CallString,PC) -> P.Instruction -> (w,w) -> v -> v
    , setup   :: P.Program -> P.ClassId -> P.MethodId -> v
    , project :: P.Program -> P.ClassId -> P.MethodId -> Int -> w -> v -> v
    , extend  :: P.Program -> P.ClassId -> Int -> w -> v -> v -> v
}

data Flow v w = Flow {
    lattice  :: SemiLattice v
  , transfer :: Transfer v w
}


-- queries

class HasIndexQ w        where hasIndexQ :: w -> (Int, Int)
class HasTypeQ w         where hasTypeQ :: w -> Var -> P.Type

class MayShareQ w        where mayShareQ :: w -> Var -> Var -> Bool
class MaySharesWithQ w   where maySharesWithQ :: w -> Var -> [Var]
class MaySharingVarsQ w  where maySharingVarsQ :: w -> [(Var,Var)]

class MayReachQ w        where mayReachQ :: w -> Var -> Var -> Bool
class MayReachesQ w      where mayReachesQ :: w -> Var -> [Var]
class MayReachingVarsQ w where mayReachingVarsQ :: w -> [(Var,Var)]
class IsAcyclicQ w       where isAcyclicQ :: w -> Var -> Bool
class AcyclicVarsQ w     where acyclicVarsQ :: w -> [Var]

class MayAliasQ w        where mayAliasQ :: w -> Var -> Var -> Bool


--data QueryV v = QueryV {
    --hasIndex      :: v -> Maybe (Int,Int)
  --, hasStkIndex   :: v -> Int -> Maybe Int
  --, hasType       :: v -> Var -> Maybe P.Type
  --, mayShare      :: v -> Var -> Var -> Maybe Bool
  --, maySharesWith :: v -> Var -> Maybe [Var]
  --, isAcyclic     :: v -> Var -> Maybe Bool
  --, mayReach      :: v -> Var -> Var -> Maybe Bool
  --, mayReaches    :: v -> Var -> Maybe [Var]
  --, isCyclic      :: v -> Var -> Maybe Bool
--}

--data Query = Query {
  --hasIndexQ        :: (Int,Int)
  --, hasStkIndexQ   :: Int -> Int
  --, hasTypeQ       :: Var -> P.Type
  --, mayShareQ      :: Var -> Var -> Bool
  --, maySharesWithQ :: Var -> [Var]
  --, isAcyclicQ     :: Var -> Bool
  --, mayReachQ      :: Var -> Var -> Bool
  --, mayReachesQ    :: Var -> [Var]
  --, isCyclicQ      :: Var -> Bool
--}

--runQueryV :: v -> QueryV v -> Query
--runQueryV v (QueryV ix sx ty sh sh' ac rh rh' cy) = Query qix qsx qty qsh qsh' qac qrh qrh' qcy
  --where
    --qix      = error "runQueryV: index"    `fromMaybe` ix v
    --qsx  n   = error "runQueryV: stkindex" `fromMaybe` sx v n
    --qty  x   = error "runQueryV: type"     `fromMaybe` ty v x
    --qsh  x y = error "runQueryV: sharing"  `fromMaybe` sh v x y
    --qsh' x   = error "runQueryV: sharings" `fromMaybe` sh' v x
    --qac  x   = error "runQueryV: acyclic"  `fromMaybe` ac v x
    --qrh  x y = error "runQueryV: reach"    `fromMaybe` rh v x y
    --qrh' x   = error "runQueryV: reaches"  `fromMaybe` rh' v x
    --qcy  x   = error "runQueryV: cyclic"   `fromMaybe` cy v x

--defaultQueryV :: QueryV v
--defaultQueryV = QueryV {
    --hasIndex      = const Nothing
  --, hasStkIndex   = \_ _   -> Nothing
  --, hasType       = \_ _   -> Nothing
  --, mayShare      = \_ _ _ -> Nothing
  --, maySharesWith = \_ _   -> Nothing
  --, isAcyclic     = \_ _   -> Nothing
  --, mayReach      = \_ _ _ -> Nothing
  --, mayReaches    = \_ _   -> Nothing
  --, isCyclic      = \_ _   -> Nothing
  --}


--infixl 7 :>:,:*:
--data a :>: b = a :>: b deriving (Eq, Ord)
--data a :*: b = a :*: b deriving (Eq, Ord)

--instance (Show a, Show b) => Show (a :>: b) where
  --show (a :>: b)  = show $ string "---" <$> string (show a) <$> string ":>:" <$> string (show b) <$> string "---"
--instance (Show a, Show b) => Show (a :*: b) where
  --show (a :*: b)  = show $ string "---" <$> string (show a) <$> string ":*:" <$> string (show b) <$> string "---"


---- left to right dependency !
--mkFlow2 :: (Show v, Show v') => P.Program -> Flow v -> Flow v' -> Flow (v :*: v')
--mkFlow2 p (Flow lat1 tran1 quer1) (Flow lat2 tran2 quer2) = Flow lat3 tran3 quer3
  --where
    --lat3  = SemiLattice name3 bot3 join3
    --tran3 = Transfer transf3 setup3 project3 extend3
    --quer3 = QueryV hasIndex3 hasStkIndex3 hasType3 mayShare3 maySharesWith3 isAcyclic3 mayReach3 mayReaches3 isCyclic3

    --name3 = name lat1 ++ 'X': name lat2
    --bot3  = bot lat1 :*: bot lat2
    --join3 _ (v1 :*: v2) (v1' :*: v2') = join lat1 p v1 v1' :*: join lat2 p v2 v2'

    --hasIndex3      (v :*: v')     = hasIndex      quer1 v     `mplus` hasIndex      quer2 v'
    --hasStkIndex3   (v :*: v') n   = hasStkIndex   quer1 v n   `mplus` hasStkIndex   quer2 v' n
    --hasType3       (v :*: v') x   = hasType       quer1 v x   `mplus` hasType       quer2 v' x
    --mayShare3      (v :*: v') x y = mayShare      quer1 v x y `mplus` mayShare      quer2 v' x y
    --maySharesWith3 (v :*: v') x   = maySharesWith quer1 v x   `mplus` maySharesWith quer2 v' x 
    --isAcyclic3     (v :*: v') x   = isAcyclic     quer1 v x   `mplus` isAcyclic     quer2 v' x
    --mayReach3      (v :*: v') x y = mayReach      quer1 v x y `mplus` mayReach      quer2 v' x y
    --mayReaches3    (v :*: v') x   = mayReaches    quer1 v x   `mplus` mayReaches    quer2 v' x
    --isCyclic3      (v :*: v') x   = isCyclic      quer1 v x   `mplus` isCyclic      quer2 v' x

    --setup3 _ cn mn = setup tran1 p cn mn :*: setup tran2 p cn mn

    ----runQueryV' v = runQueryV v quer3

    --project3 _ q cn mn i (v1 :*: v2) = w1 :*: w2
      --where
        --w1 = project tran1 p q cn mn i v1
        --w2 = project tran2 p q cn mn i v2
    
    --extend3 _ q cn i (old1 :*: old2) (new1 :*: new2) = v1 :*: v2
      --where
        --v1 = extend tran1 p q cn i old1 new1
        --v2 = extend tran2 p q cn i old2 new2

    --transf3 _ q ins (v1 :*: v2) = w1 :*: w2
      --where
        --w1 = transf tran1 p q ins v1
        --w2 = transf tran2 p q ins v2

--mkFlow2' :: (Show v, Show v') => P.Program -> Flow v -> Flow v' -> Flow (v :>: v')
--mkFlow2' p (Flow lat1 tran1 quer1) (Flow lat2 tran2 quer2) = Flow lat3 tran3 quer3
  --where
    --lat3  = SemiLattice name3 bot3 join3
    --tran3 = Transfer transf3 setup3 project3 extend3
    --quer3 = QueryV hasIndex3 hasStkIndex3 hasType3 mayShare3 maySharesWith3 isAcyclic3 mayReach3 mayReaches3 isCyclic3

    --name3 = name lat1 ++ 'X': name lat2
    --bot3  = bot lat1 :>: bot lat2
    --join3 _ (v1 :>: v2) (v1' :>: v2') = join lat1 p v1 v1' :>: join lat2 p v2 v2'

    --hasIndex3      (v :>: v')     = hasIndex      quer1 v     `mplus` hasIndex      quer2 v'
    --hasStkIndex3   (v :>: v') n   = hasStkIndex   quer1 v n   `mplus` hasStkIndex   quer2 v' n
    --hasType3       (v :>: v') x   = hasType       quer1 v x   `mplus` hasType       quer2 v' x
    --mayShare3      (v :>: v') x y = mayShare      quer1 v x y `mplus` mayShare      quer2 v' x y
    --maySharesWith3 (v :>: v') x   = maySharesWith quer1 v x   `mplus` maySharesWith quer2 v' x 
    --isAcyclic3  (v :>: v') x      = isAcyclic  quer1 v x   `mplus` isAcyclic  quer2 v' x
    --mayReach3   (v :>: v') x y = mayReach   quer1 v x y `mplus` mayReach   quer2 v' x y
    --mayReaches3 (v :>: v') x   = mayReaches quer1 v x   `mplus` mayReaches quer2 v' x
    --isCyclic3   (v :>: v') x   = isCyclic   quer1 v x   `mplus` isCyclic   quer2 v' x

    --setup3 _ cn mn = setup tran1 p cn mn :>: setup tran2 p cn mn

    --runQueryV' v = runQueryV v quer3

    --project3 _ q cn mn i (v1 :>: v2) = w1 :>: w2
      --where
        --w1 = project tran1 p q cn mn i v1
        --w2 = project tran2 p q cn mn i v2
    
    --extend3 _ q cn i (old1 :>: old2) (new1 :>: new2) = v1 :>: v2
      --where
        --v1 = extend tran1 p q cn i old1 new1
        --v2 = extend tran2 p q cn i old2 new2

    --transf3 _ _ ins (v1 :>: v2) = w1 :>: w2
      --where
        --w1 = transf tran1 p q1 ins v1
        --w2 = transf tran2 p q2 ins v2
        --q1 = runQueryV' (v1 :>: v2)
        --q2 = runQueryV' (w1 :>: v2)

