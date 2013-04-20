-- | This module provides common queries for a JBC 'Program'.
module Jat.Program.Fun
  (
    parseProgram
  , classes
  , methods
  , theClass
  , supClassOf
  , supClassesOf
  , subClassesOf
  , isSuper
  , theMethod
  , seesMethodIn
  , instructions
  , instruction
  , hasFields
  , theLeastCommonSupClass
  , leastCommonSupClass
  , properReachableClasses
  , reachableClasses
  )
where

import Jat.Program.Data
import Jat.Program.Parser

import Data.Maybe (isNothing,fromMaybe)
import qualified Data.Array as A
import qualified Data.Map as M
import qualified Data.Set as S

-- | Parses and initializes a 'Program'.
parseProgram :: String -> Program
parseProgram = initP . fromString

-- | Returns the classes as identfiers of a 'Program'.
classes :: Program -> [ClassId]
classes (P cp) = M.keys cp

-- | Returns the methods of a 'Program'.
methods :: Program -> [(ClassId,MethodId)]
methods p = concatMap (\cn -> [(cn,mn) | mn <- M.keys . methodPool $ theClass p cn]) (classes p)

-- | Returns the 'Class' of a given Id.
-- Returns an error if the id does not exist.
theClass :: Program -> ClassId -> Class
theClass (P cp) cn = errmsg `fromMaybe` M.lookup cn cp
  where errmsg = error $ "Jat.Program.Op.theClass: class not found: " ++ show cn

-- | Returns d if c <1 d holds, Nothing otherwise.
supClassOf :: Program -> ClassId -> Maybe ClassId
supClassOf p = supClass . theClass p

-- | Returns ordered list of (maybe non-proper) superclasses.
supClassesOf :: Program -> ClassId -> [ClassId]
supClassesOf p = supClasses . theClass p

-- | Returns (unordered) list of (maybe non-proper) subclasses.
subClassesOf :: Program -> ClassId -> [ClassId]
subClassesOf p = subClasses . theClass p

-- | Returns True if d>=c holds.
isSuper :: Program -> ClassId -> ClassId -> Bool
isSuper p cn cn' =  cn `elem` supClassesOf p cn'

-- | Returns the 'Method' of a given Id.
-- Returns an error if the id does not exist.
theMethod :: Program -> ClassId -> MethodId -> Method
theMethod p cn mn = errmsg `fromMaybe` (M.lookup mn . methodPool $ theClass p cn)
  where errmsg = error $ "Jat.Program.Op.theMethod: method not found: " ++ show (cn,mn)

-- | This implements dynamic invoke and returns the first method defined wrt to
-- the type hierarchy going upwards starting from the given class id.
seesMethodIn :: Program -> ClassId -> MethodId -> (ClassId, Method)
seesMethodIn p cn mn = 
  case isDefined of
    (cn', _):_ -> (cn', theMethod p cn' mn)
    _         -> error $ "Jat.Program.Op.seesMethod: no such method defined" ++ show (cn,mn)
  where
    cns       = supClassesOf p cn
    isDefined = dropWhile (isNothing . snd) $ map (\lcn -> (lcn, methodOf' lcn mn)) cns
    methodOf' cn' mn' = M.lookup mn' . methodPool $ theClass p cn'

-- | Returns the instructions of method.
instructions :: Program -> ClassId -> MethodId -> A.Array Int Instruction
instructions p cn mn = methodInstructions $ theMethod p cn mn

-- | Returns the ith instruction.
instruction :: Program -> ClassId -> MethodId -> Int -> Instruction
instruction p cn mn i = (A.!i) $ instructions p cn mn

-- | Returns all fields (including fields of superclasses) of a class.
hasFields :: Program -> ClassId -> [(FieldId, ClassId, Type)]
hasFields p = hasFieldz . theClass p

-- | Extracts the least common super class.
theLeastCommonSupClass :: Program -> ClassId -> ClassId -> ClassId
theLeastCommonSupClass p cn cn' = errmsg `fromMaybe` leastCommonSupClass p cn cn'
  where errmsg = error $ "Jat.Program.Op.theLeastCommonSupClass: common supperclass expected: " ++ show (cn,cn')

-- | Returns the least common super class if it exists.
-- It is not necessary that there exists a dedicated object class.
leastCommonSupClass :: Program -> ClassId -> ClassId -> Maybe ClassId
leastCommonSupClass p cn cn' = meet cns dns
  where
    cns                        = supClassesOf p cn
    dns                        = supClassesOf p cn'
    meet [] []                 = Nothing
    meet (c:_) (d:_) | c == d  = Just c
    meet (_:cs) []             = meet cs dns
    meet cs (_:ds)             = meet cs ds
    
-- | Returns all reachable classes wrt. to subclasses and fieldtables.
reachableClasses :: Program -> ClassId -> [ClassId]
reachableClasses p cn = S.elems $ reachableClasses' p S.empty (S.singleton cn) 

-- | Same as reachableClasses but the queried 'Class' is only member of the
-- returned list if it is reachable from another class.
properReachableClasses :: Program -> ClassId -> [ClassId]
properReachableClasses p cn = S.elems $ reachableClasses' p S.empty initial
  where initial = S.fromList [tp | (_,_,RefType tp) <- hasFields p cn]

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
