-- | This module provides common queries for a JBC 'Program'.
module Jinja.Program.Fun
  (
    parseProgram
  , classes
  , methods
  , theClass
  , supClassOf
  , supClassesOf
  , subClassesOf
  , isSuper
  , isSuber
  , theMethod
  , isMethodCall
  , isReturn
  , isRefType
  , isPrimitiveType
  , seesMethodIn
  , instructions
  , instruction
  , successors
  , hasFields
  , field
  , theLeastCommonSupClass
  , leastCommonSupClass

  -- type based shape properties
  , RefKind (..)
  , reachableClasses
  , properReachableClasses

  , isAcyclicClass
  , areSharingClasses
  , areReachingClasses

  , isAcyclicType
  , areSharingTypes
  , areReachingTypes
  , areRelatedTypes
  , singleCyclicField
  , singleReachingField
  )
where

import Jinja.Program.Data
import Jinja.Program.Parser

import Data.Maybe (isNothing,fromMaybe)
import qualified Data.Array as A
import qualified Data.Map as M
import qualified Data.Set as S

--import Debug.Trace

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

isSuber :: Program -> ClassId -> ClassId -> Bool
isSuber p cn cn' =  cn `elem` subClassesOf p cn'

-- | Returns the 'Method' of a given Id.
-- Returns an error if the id does not exist.
theMethod :: Program -> ClassId -> MethodId -> Method
theMethod p cn mn = errmsg `fromMaybe` (M.lookup mn . methodPool $ theClass p cn)
  where errmsg = error $ "Jat.Program.Op.theMethod: method not found: " ++ show (cn,mn)

isMethodCall :: Instruction -> Bool
isMethodCall (Invoke _ _) = True
isMethodCall _            = False

isReturn :: Instruction -> Bool
isReturn Return = True
isReturn _      = False

isRefType :: Type -> Bool
isRefType (RefType _) = True
isRefType _           = False

isPrimitiveType :: Type -> Bool
isPrimitiveType = not . isRefType

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

-- | Returns the successors for a labeled instruction.
-- TODO take nulltype into account ?
successors :: Instruction -> Int -> [Int]
successors (IfFalse j) pc = [pc+1, pc+j]
successors (Goto j)    pc = [pc+j]
successors Return      _  = []
successors _           pc = [pc+1]

-- | Returns all fields (including fields of superclasses) of a class.
hasFields :: Program -> ClassId -> [(FieldId, ClassId, Type)]
hasFields p = hasFieldz . theClass p

theField :: Program -> ClassId -> FieldId -> Field
theField p cn fn = errmsg `fromMaybe` M.lookup fn fp
  where 
    fp = fieldPool $ theClass p cn
    errmsg = error "Jat.Program.Fun.theField: unexpected field query." 

field :: Program -> ClassId -> FieldId -> (FieldId, Type)
field p cn fn = (fn, fieldType $ theField p cn fn)

{-field :: Program -> ClassId -> FieldId -> (FieldId, Type)-}
{-field p cn fn = errmsg `fromMaybe` (fld >>=  (fn, fieldType fld))-}
  {-where -}
    {-fld    = M.lookup fn (fieldPool $ theClass p cn)-}
    {-errmsg = "Jat.Program.Fun.field: unexpected field query"-}

{-field :: Program -> ClassId -> FieldId -> Maybe (ClassId, Type)-}
{-field p cn fn = lookup fn $ map (\(f,c,t) -> (f,(c,t))) fields-}
  {-where fields = hasFields p cn-}

-- | Extracts the least common super class.
theLeastCommonSupClass :: Program -> ClassId -> ClassId -> ClassId
theLeastCommonSupClass p cn cn' = errmsg `fromMaybe` leastCommonSupClass p cn cn'
  where errmsg = error $ "Jat.Program.Op.theLeastCommonSupClass: common supperclass expected: " ++ show (cn,cn')

-- | Returns the least common super class if it exists.
-- It is not necessary that there exists a dedicated object class.
leastCommonSupClass :: Program -> ClassId -> ClassId -> Maybe ClassId
leastCommonSupClass p cn dn = meet cns dns
  where
    cns                        = supClassesOf p cn
    dns                        = supClassesOf p dn
    meet [] []                 = Nothing
    meet (c:_) (d:_) | c == d  = Just c
    meet (_:cs) []             = meet cs dns
    meet cs (_:ds)             = meet cs ds


-- shape properties
-- we refine type information if obtained from an instance or class variable
data RefKind =
  InstanceKind ClassId
  | ClassVarKind ClassId 
  | VariableKind ClassId 
  deriving Eq

ofClass :: RefKind -> ClassId
ofClass (InstanceKind cn) = cn
ofClass (ClassVarKind cn) = cn
ofClass (VariableKind cn) = cn

fieldClasses :: Program -> ClassId -> [ClassId]
fieldClasses p cn = [tp | (_,_,RefType tp) <- hasFields p cn]
    
-- | Returns all reachable classes wrt. to subclasses and fieldtables.
reachableClasses :: Program -> RefKind -> S.Set ClassId
reachableClasses p (InstanceKind cn) = reachableClasses' p (S.singleton cn) (S.fromList $ fieldClasses p cn)
reachableClasses p cn                = reachableClasses' p S.empty (S.singleton $ ofClass cn)

-- | Same as reachableClasses but the queried 'Class' is only member of the
-- returned list if it is reachable from another class.
properReachableClasses :: Program -> RefKind -> S.Set ClassId
properReachableClasses p (InstanceKind cn) = reachableClasses' p S.empty (S.fromList $ fieldClasses p cn)
properReachableClasses p cn                = reachableClasses' p S.empty (S.unions . map (S.fromList . fieldClasses p) $ subClassesOf p $ ofClass cn)

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



-- checks if type is acyclic
isAcyclicClass :: Program -> RefKind -> Bool
isAcyclicClass p (InstanceKind cn) = cn `S.notMember` properReachableClasses p (InstanceKind cn)
isAcyclicClass p (ClassVarKind cn) = all  (isAcyclicClass p . InstanceKind) $ subClassesOf p cn
isAcyclicClass p (VariableKind cn) = all' (isAcyclicClass p . InstanceKind) $ reachableClasses p (VariableKind cn)
  where all' f = S.foldr (\a -> (f a &&)) True


areSharingClasses :: Program -> RefKind -> RefKind -> Bool
areSharingClasses p cn1 cn2 = not . S.null $ cns1 `S.intersection` cns2
  where
    cns1 = reachableClasses p cn1
    cns2 = reachableClasses p cn2

areReachingClasses :: Program -> RefKind -> RefKind -> Bool
areReachingClasses p cn1 cn2 = not . S.null $ cns1 `S.intersection` cns2
  where
    cns1 = properReachableClasses p cn1
    cns2 = case cn2 of
      (InstanceKind cn) -> S.singleton cn
      _                 -> S.fromList $ subClassesOf p $ ofClass cn2

{-isTreeShapedType :: Program -> Type -> Bool-}
{-isTreeShapedType p ty | isAcyclicType p ty = False-}
{-isTreeShapedType p (RefType cn) = isTreeShaped' S.empty [cn]-}
  {-where-}
    {-isTreeShaped' _ [] = True-}
    {-isTreeShaped' visited (cn':cns) | cn' `S.member` visited = isTreeShaped' visited cns-}
    {-isTreeShaped' visited (cn':cns) = treeShaped cn' && isTreeShaped' visited' (clazzes cn' ++ cns)-}
      {-where visited' = cn' `S.insert` visited-}

    {-clazzes cn'       = subClassesOf p cn' ++ hasRefFields cn'-}
    {-hasRefFields cn'  = [ tp | (_,_,RefType tp) <- hasFields p cn']-}
    {-treeShaped cn'    = case reaches of-}
      {-[]     -> True-}
      {-(x:xs) -> foldl S.intersection x xs == S.empty-}
      {-where reaches = reachableClasses p `fmap` hasRefFields cn'-}
{-isTreeShapedType _ _ = False-}

{-areSharingTypes :: Program -> Type -> Type -> Bool-}
{-areSharingTypes p (RefType cn1) (RefType cn2) = not . S.null $ tys1 `S.intersection` tys2-}
  {-where -}
    {-tys1 = reachableClasses p cn1-}
    {-tys2 = reachableClasses p cn2-}
{-areSharingTypes _ _ _                         = False-}

-- cn <= cn1, cn' <= cn2 and cn ->+ cn'
{-areReachingTypes :: Program -> Type -> Type -> Bool-}
{-areReachingTypes p (RefType cn1) (RefType cn2) = not . S.null $ tys1 `S.intersection` tys2-}
  {-where-}
    {-tys1 = properReachableClasses p cn1-}
    {-tys2 = S.fromList $ subClassesOf p cn2-}
{-areReachingTypes _ _ _                         = False-}

isAcyclicType :: Program -> Type -> Bool
isAcyclicType p (RefType cn) = isAcyclicClass p (VariableKind cn)
isAcyclicType _ _            = True

areSharingTypes :: Program -> Type -> Type -> Bool
areSharingTypes p (RefType cn1) (RefType cn2) = areSharingClasses p (VariableKind cn1) (VariableKind cn2)
areSharingTypes _ _ _                         = False

areReachingTypes :: Program -> Type -> Type -> Bool
areReachingTypes p (RefType cn1) (RefType cn2) = areReachingClasses p (VariableKind cn1) (VariableKind cn2)
areReachingTypes _ _ _                         = False


areRelatedTypes :: Program -> Type -> Type -> Bool
areRelatedTypes _ BoolType BoolType           = True
areRelatedTypes _ IntType IntType             = True
areRelatedTypes _ Void Void                   = True
areRelatedTypes p (RefType cn1) (RefType cn2) =
  isSuper p cn1 cn2 || isSuber p cn1 cn2
areRelatedTypes _ _ _                          = False


-- given cn, checks for all cn' <= cn that there exists no field different from (dn,fn) that is statically not acyclic
singleCyclicField :: Program -> ClassId -> (ClassId,FieldId) -> Bool
singleCyclicField p cn (dn,fn) = and [ not (isAcyclicType p ty') | (fn',dn',ty') <- fds, dn' /= dn || fn' /= fn]
  where fds = concatMap (hasFields p) $ subClassesOf p cn

-- given cn, checks for all cn' <= cn that there exists no field different from (dn,fn) that statically reaches ty
singleReachingField :: Program -> ClassId -> (ClassId,FieldId) -> Type -> Bool
singleReachingField p cn (dn,fn) ty = and [ areReachingTypes p ty' ty | (fn',dn',ty') <- fds, dn' /= dn || fn' /= fn]
  where fds = concatMap (hasFields p) $ subClassesOf p cn

