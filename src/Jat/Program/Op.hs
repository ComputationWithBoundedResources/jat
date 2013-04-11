module Jat.Program.Op 
  (
    classes
  , methods
  , theClass
  , supClassOf
  , supClassesOf
  , subClassesOf
  , isSuper
  , isRelative
  , theMethod
  , seesMethodIn
  , instructions
  , instruction
  , hasFields
  , theLeastCommonSupClass
  , leastCommonSupClass
  , properReachableClasses
  , reachableClasses
  , parseProgram
  , isBackJump
  )
where

import Jat.Program.Data
import Jat.Program.Parser

import Data.Maybe (isNothing,fromMaybe)
import qualified Data.Map as M
import qualified Data.Array as A
import qualified Data.Set as S

parseProgram :: String -> Program
parseProgram = initP . fromString

classes :: Program -> [ClassId]
classes (P cp) = M.keys cp

methods :: Program -> [(ClassId,MethodId)]
methods p = concatMap (\cn -> [(cn,mn) | mn <- M.keys . methodPool $ theClass p cn]) (classes p)

-- returns the 'class' of a given id
theClass :: Program -> ClassId -> Class
theClass (P cp) cn = errmsg `fromMaybe` M.lookup cn cp
  where errmsg = error $ "Jat.Program.Op.theClass: class not found: " ++ show cn

-- returns d if c <1 d holds
-- returns Nothing otherwise
supClassOf :: Program -> ClassId -> Maybe ClassId
supClassOf p = supClass . theClass p

-- returns ordered list of superclasses
supClassesOf :: Program -> ClassId -> [ClassId]
supClassesOf p = supClasses . theClass p

-- returns (unordered) list of subclasses
subClassesOf :: Program -> ClassId -> [ClassId]
subClassesOf p = subClasses . theClass p

-- returns True if d>=c holds
isSuper :: Program -> ClassId -> ClassId -> Bool
isSuper p cn cn' =  cn `elem` supClassesOf p cn'

theMethod :: Program -> ClassId -> MethodId -> Method
theMethod p cn mn = errmsg `fromMaybe` (M.lookup mn . methodPool $ theClass p cn)
  where errmsg = error $ "Jat.Program.Op.theMethod: method not found: " ++ show (cn,mn)

-- returns the first method defined wrt to the type hierarchy going upwards starting from cn
seesMethodIn :: Program -> ClassId -> MethodId -> (ClassId, Method)
seesMethodIn p cn mn = 
  case isDefined of
    (cn', _):_ -> (cn', theMethod p cn' mn)
    _         -> error $ "Jat.Program.Op.seesMethod: no such method defined" ++ show (cn,mn)
  where
    cns       = supClassesOf p cn
    isDefined = dropWhile (isNothing . snd) $ map (\lcn -> (lcn, methodOf' lcn mn)) cns
    methodOf' cn' mn' = M.lookup mn' . methodPool $ theClass p cn'

instructions :: Program -> ClassId -> MethodId -> A.Array Int Instruction
instructions p cn mn = methodInstructions $ theMethod p cn mn

instruction :: Program -> ClassId -> MethodId -> Int -> Instruction
instruction p cn mn i = (A.!i) $ instructions p cn mn

-- returns all fields (including superclasses) of a class
hasFields :: Program -> ClassId -> [(FieldId, ClassId, Type)]
hasFields p = hasFieldz . theClass p

theLeastCommonSupClass :: Program -> ClassId -> ClassId -> ClassId
theLeastCommonSupClass p cn cn' = errmsg `fromMaybe` leastCommonSupClass p cn cn'
  where errmsg = error $ "Jat.Program.Op.theLeastCommonSupClass: common supperclass expected: " ++ show (cn,cn')

leastCommonSupClass :: Program -> ClassId -> ClassId -> Maybe ClassId
leastCommonSupClass p cn cn' = meet cns dns
  where
    cns                        = supClassesOf p cn
    dns                        = supClassesOf p cn'
    meet [] []                 = Nothing
    meet (c:_) (d:_) | c == d  = Just c
    meet (_:cs) []             = meet cs dns
    meet cs (_:ds)             = meet cs ds

-- same as reachableClasses but `cn` is only member of the set if reachable from another class
properReachableClasses :: Program -> ClassId -> [ClassId]
properReachableClasses p cn = S.elems $ reachableClasses' p S.empty initial
  where initial = S.fromList [tp | (_,_,RefType tp) <- hasFields p cn]

-- returns all classes reachable from the type hierarchy wrt. subclasses and fieldtables
reachableClasses :: Program -> ClassId -> [ClassId]
reachableClasses p cn = S.elems $ reachableClasses' p S.empty (S.singleton cn) 

reachableClasses' :: Program -> S.Set ClassId -> S.Set ClassId -> S.Set ClassId
reachableClasses' p acc new = 
  let new' = S.fold (\cn -> (f cn `S.union`)) S.empty new
      acc' = acc `S.union` new'
  in
  if fix acc acc'
    then acc
    else reachableClasses' p acc' new'
  where
    f cn      = subs cn `S.union`  fds cn
    subs cn   = S.fromList $ subClassesOf p cn
    fds cn    = S.fromList [tp | (_,_,RefType tp) <- hasFields p cn]
    fix s1 s2 = S.size s1 == S.size s2

isBackJump :: Program -> ClassId -> MethodId -> Int -> Bool
isBackJump p cn mn pc = case instruction p cn mn pc of
  Goto i -> i < 0
  _      -> False
