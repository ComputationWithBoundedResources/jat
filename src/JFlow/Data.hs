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


data QueryV v = QueryV {
    hasIndex      :: v -> Maybe (Int,Int)
  , hasStkIndex   :: v -> Int -> Maybe Int
  , hasType       :: v -> Var -> Maybe P.Type
  , mayShare      :: v -> Var -> Var -> Maybe Bool
  , maySharesWith :: v -> Var -> Maybe [Var]
  , isTreeShaped  :: v -> Var -> Maybe Bool
}

data Query = Query {
    hasIndexQ      :: (Int,Int)
  , hasStkIndexQ   :: Int -> Int
  , hasTypeQ       :: Var -> P.Type
  , mayShareQ      :: Var -> Var -> Bool
  , maySharesWithQ :: Var -> [Var]
  , isTreeShapedQ  :: Var -> Bool
}

runQueryV :: v -> QueryV v -> Query
runQueryV v (QueryV ix sx ty sh sh' ts) = Query qix qsx qty qsh qsh' qts
  where
    qix      = error "runQueryV: index"      `fromMaybe` ix v
    qsx  n   = error "runQueryV: stkindex"   `fromMaybe` sx v n
    qty  x   = error "runQueryV: type"       `fromMaybe` ty v x
    qsh  x y = error "runQueryV: sharing"    `fromMaybe` sh v x y
    qsh' x   = error "runQueryV: sharings"   `fromMaybe` sh' v x
    qts  x   = error "runQueryV: treeshaped" `fromMaybe` ts v x

defaultQueryV :: QueryV v
defaultQueryV = QueryV {
    hasIndex      = const Nothing
  , hasStkIndex   = \_ _   -> Nothing
  , hasType       = \_ _   -> Nothing
  , mayShare      = \_ _ _ -> Nothing
  , maySharesWith = \_ _   -> Nothing
  , isTreeShaped  = \_ _   -> Nothing
  }

data SemiLattice v = SemiLattice {
    name :: String
  , bot  :: v
  , join :: P.Program -> v -> v -> v
}

data Transfer v = Transfer {
      transf  :: P.Program -> Query -> P.Instruction -> v -> v
    , setup   :: P.Program -> P.ClassId -> P.MethodId -> v
    , project :: P.Program -> Query -> P.ClassId -> P.MethodId -> Int -> v -> v
    , extend  :: P.Program -> Query -> P.ClassId -> Int -> v -> v -> v
}

data Flow v = Flow {
    lattice  :: SemiLattice v
  , transfer :: Transfer v
  , query    :: QueryV v 
}

infixl 7 :>:,:*:
data a :>: b = a :>: b deriving (Eq, Ord)
data a :*: b = a :*: b deriving (Eq, Ord)

instance (Show a, Show b) => Show (a :>: b) where
  show (a :>: b)  = show $ string "---" <$> string (show a) <$> string ":>:" <$> string (show b) <$> string "---"
instance (Show a, Show b) => Show (a :*: b) where
  show (a :*: b)  = show $ string "---" <$> string (show a) <$> string ":*:" <$> string (show b) <$> string "---"


-- left to right dependency !
mkFlow2 :: (Show v, Show v') => P.Program -> Flow v -> Flow v' -> Flow (v :*: v')
mkFlow2 p (Flow lat1 tran1 quer1) (Flow lat2 tran2 quer2) = Flow lat3 tran3 quer3
  where
    lat3  = SemiLattice name3 bot3 join3
    tran3 = Transfer transf3 setup3 project3 extend3
    quer3 = QueryV hasIndex3 hasStkIndex3 hasType3 mayShare3 maySharesWith3 isTreeShaped3

    name3 = name lat1 ++ 'X': name lat2
    bot3  = bot lat1 :*: bot lat2
    join3 _ (v1 :*: v2) (v1' :*: v2') = join lat1 p v1 v1' :*: join lat2 p v2 v2'

    hasIndex3      (v :*: v')     = hasIndex      quer1 v     `mplus` hasIndex      quer2 v'
    hasStkIndex3   (v :*: v') n   = hasStkIndex   quer1 v n   `mplus` hasStkIndex   quer2 v' n
    hasType3       (v :*: v') x   = hasType       quer1 v x   `mplus` hasType       quer2 v' x
    mayShare3      (v :*: v') x y = mayShare      quer1 v x y `mplus` mayShare      quer2 v' x y
    maySharesWith3 (v :*: v') x   = maySharesWith quer1 v x   `mplus` maySharesWith quer2 v' x 
    isTreeShaped3  (v :*: v') x   = isTreeShaped  quer1 v x   `mplus` isTreeShaped  quer2 v' x

    setup3 _ cn mn = setup tran1 p cn mn :*: setup tran2 p cn mn

    --runQueryV' v = runQueryV v quer3

    project3 _ q cn mn i (v1 :*: v2) = w1 :*: w2
      where
        w1 = project tran1 p q cn mn i v1
        w2 = project tran2 p q cn mn i v2
    
    extend3 _ q cn i (old1 :*: old2) (new1 :*: new2) = v1 :*: v2
      where
        v1 = extend tran1 p q cn i old1 new1
        v2 = extend tran2 p q cn i old2 new2

    transf3 _ q ins (v1 :*: v2) = w1 :*: w2
      where
        w1 = transf tran1 p q ins v1
        w2 = transf tran2 p q ins v2

mkFlow2' :: (Show v, Show v') => P.Program -> Flow v -> Flow v' -> Flow (v :>: v')
mkFlow2' p (Flow lat1 tran1 quer1) (Flow lat2 tran2 quer2) = Flow lat3 tran3 quer3
  where
    lat3  = SemiLattice name3 bot3 join3
    tran3 = Transfer transf3 setup3 project3 extend3
    quer3 = QueryV hasIndex3 hasStkIndex3 hasType3 mayShare3 maySharesWith3 isTreeShaped3

    name3 = name lat1 ++ 'X': name lat2
    bot3  = bot lat1 :>: bot lat2
    join3 _ (v1 :>: v2) (v1' :>: v2') = join lat1 p v1 v1' :>: join lat2 p v2 v2'

    hasIndex3      (v :>: v')     = hasIndex      quer1 v     `mplus` hasIndex      quer2 v'
    hasStkIndex3   (v :>: v') n   = hasStkIndex   quer1 v n   `mplus` hasStkIndex   quer2 v' n
    hasType3       (v :>: v') x   = hasType       quer1 v x   `mplus` hasType       quer2 v' x
    mayShare3      (v :>: v') x y = mayShare      quer1 v x y `mplus` mayShare      quer2 v' x y
    maySharesWith3 (v :>: v') x   = maySharesWith quer1 v x   `mplus` maySharesWith quer2 v' x 
    isTreeShaped3  (v :>: v') x   = isTreeShaped  quer1 v x   `mplus` isTreeShaped  quer2 v' x

    setup3 _ cn mn = setup tran1 p cn mn :>: setup tran2 p cn mn

    runQueryV' v = runQueryV v quer3

    project3 _ q cn mn i (v1 :>: v2) = w1 :>: w2
      where
        w1 = project tran1 p q cn mn i v1
        w2 = project tran2 p q cn mn i v2
    
    extend3 _ q cn i (old1 :>: old2) (new1 :>: new2) = v1 :>: v2
      where
        v1 = extend tran1 p q cn i old1 new1
        v2 = extend tran2 p q cn i old2 new2

    transf3 _ _ ins (v1 :>: v2) = w1 :>: w2
      where
        w1 = transf tran1 p q1 ins v1
        w2 = transf tran2 p q2 ins v2
        q1 = runQueryV' (v1 :>: v2)
        q2 = runQueryV' (w1 :>: v2)

