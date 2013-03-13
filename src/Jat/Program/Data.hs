module Jat.Program.Data 
  (
    Program (..)
  , Class (..)
  , Field (..)
  , Method (..)
  , Type (..)
  , Value (..)
  , Instruction (..)
  , FieldId (..)
  , ClassId (..)
  , MethodId (..)

  , Address
  , ClassPool
  , FieldPool
  , MethodPool

  , initP
  , defaultValue
  )
where

import Jat.Utils.Pretty

import Data.Maybe (fromMaybe)
import qualified Data.Map as M
import Data.Array

-- | A 'Program' is the static representation of a JBC file complemented with
-- additional useful information.
data Program = P ClassPool deriving (Eq,Show,Read)

type ClassPool   = M.Map ClassId Class
type FieldPool   = M.Map FieldId Field
type MethodPool  = M.Map MethodId Method

type Address  = Int
data FieldId  = FieldId String deriving (Ord,Eq,Show,Read)
data ClassId  = ClassId String deriving (Ord,Eq,Show,Read)
data MethodId = MethodId String deriving (Ord,Eq,Show,Read)

data Class  = Class {
    className  :: ClassId
  , supClass   :: Maybe ClassId
  , fieldPool  :: FieldPool
  , methodPool :: MethodPool 
  , supClasses :: [ClassId]
  , subClasses :: [ClassId]
  , hasFieldz  :: [(FieldId, ClassId, Type)]
  } deriving(Eq,Show,Read)

data Field = Field {
    fieldName :: FieldId
  , fieldType :: Type
  } deriving (Eq,Show,Read)

data Method  = Method {
    methodName              :: MethodId
  , methodParams            :: [Type]
  , methodReturn            :: Type
  , maxStk                  :: Int
  , maxLoc                  :: Int
  , methodInstructions      :: Array Int Instruction
  } deriving (Eq,Show,Read)

data Type =
    BoolType
  | IntType
  | RefType ClassId
  | NullType
  | Void 
  deriving (Eq,Show,Read)

defaultValue :: Type -> Value
defaultValue BoolType    = BoolVal False
defaultValue IntType     = IntVal 0
defaultValue (RefType _) = Null
defaultValue NullType    = Null
defaultValue Void        = Unit

data Value = 
    BoolVal Bool 
  | IntVal Int 
  | RefVal Address
  | Null
  | Unit
  deriving (Eq,Show,Read)

data Instruction =
    Load Int
  | Store Int
  | Push Value
  | New ClassId
  | GetField FieldId ClassId 
  | PutField FieldId ClassId
  | CheckCast ClassId
  | Invoke  MethodId Int
  | Return
  | Pop
  | IAdd
  | Goto Int
  | CmpEq
  | CmpNeq
  | IfFalse Int
  | ISub
  | ICmpGeq
  | BNot
  | BAnd
  | BOr
  deriving (Eq,Show,Read)


-- | Computes additional information (e.g. subclasses).
initP :: Program -> Program
initP p@(P p') = P $ M.map initClass p'
  where
    initClass :: Class -> Class
    initClass c =
      let sups = supClassesf p (className c) in
      c { supClasses = sups
        , subClasses = subClassesf p (className c)
        , hasFieldz  = hasFieldzf p sups
        }

supClassesf :: Program -> ClassId -> [ClassId]
supClassesf p cn = reverse $ supClassesf' cn [cn]
  where 
    supClassesf' cn1 cns =  case supClassf p cn1 of
      Nothing  -> cns
      Just cn2 -> supClassesf' cn2 (cn2:cns)

supClassf :: Program -> ClassId -> Maybe ClassId
supClassf p = supClass . classOf p

classOf :: Program -> ClassId -> Class
classOf (P cp) cn = errMsg `fromMaybe` M.lookup cn cp
  where errMsg = error $ "Jat.Program.Data.classOf: element not found" ++ show cn

isSuper :: Program -> ClassId -> ClassId -> Bool
isSuper p cn cn' = cn `elem` supClassesf p cn'

subClassesf :: Program -> ClassId -> [ClassId]
subClassesf p@(P cp) cn = filter (isSuper p cn) (M.keys cp)

hasFieldzf :: Program -> [ClassId] -> [(FieldId, ClassId, Type)]
hasFieldzf p = concatMap (\cn' -> fds cn' . fieldPool $ classOf p cn')
  where fds cn = M.fold (\lfd lfdt -> (fieldName lfd, cn,fieldType lfd):lfdt) []


-- pretty
instance Pretty FieldId where
  pretty (FieldId fn) = string fn
  
instance Pretty ClassId where
  pretty (ClassId cn) = string cn

instance Pretty MethodId where
  pretty (MethodId mn) = string mn

instance Pretty Class where
  pretty c = text "Class:" <$> indent 2 prettyName <$> indent 2 prettyBody
    where
      prettyName    = text "Name:" <+> pretty (className c)
      prettyBody    = text "ClassBody:" <$> indent 2 prettySuper <$> indent 2 prettyFields <$> indent 2 prettyMethods
      prettySuper   = text "Superclass:" <+>  case supClass c of {Just c' -> pretty c'; Nothing -> text "<None>"}
      prettyFields  = text "Fields:" <$> indent 2 (vcat (map pretty . M.elems $ fieldPool c))
      prettyMethods = text "Methods:" <$> indent 2 (vcat (map pretty . M.elems $ methodPool c))

instance Pretty Field where
  pretty f = pretty (fieldType f) <+> pretty (fieldName f)

instance Pretty Method where
  pretty m = prettyHeader <$> indent 2 prettyParams <$> indent 2 prettyBody
    where
      prettyHeader       = text "Method:" <+> pretty (methodReturn m) <+> pretty (methodName m)
      prettyParams       = text "Parameters:" <$> (indent 2 . vcat $ map pretty (methodParams m))
      prettyBody         = text "Methodbody:" <$> indent 2 prettyMaxStack <$> indent 2 prettyMaxLoc <$> indent 2 prettyInstructions
      prettyMaxStack     = text "MaxStack:" <$> indent 2 (int $ maxStk m)
      prettyMaxLoc       = text "MaxVars:" <$> indent 2 (int $ maxLoc m)
      prettyInstructions = text "Bytecode:" <$> (indent 2 . vcat $ zipWith (\c i -> int c <+> colon <+> pretty i) [0..] (elems $ methodInstructions m))

instance Pretty Type where
  pretty BoolType     = text "bool"
  pretty IntType      = text "int"
  pretty (RefType cn) = pretty cn
  pretty (NullType)   = text "NT"
  pretty Void         = text "void"

instance Pretty Value where
  pretty (BoolVal b) = text $ show b
  pretty (IntVal i)  = int i
  pretty (RefVal a)  = int a
  pretty Null        = text "null"
  pretty Unit        = text "unit"

instance Pretty Instruction where
  pretty (Load i)         = text "Load" <+> int i
  pretty (Store i)        = text "Store" <+> int i
  pretty (Push v)         = text "Push" <+> pretty v
  pretty (New cn)         = text "New" <+> pretty cn
  pretty (GetField fn cn) = text "GetField" <+> pretty fn <+> pretty cn
  pretty (PutField fn cn) = text "PutField" <+> pretty fn <+> pretty cn
  pretty (CheckCast cn)   = text "CheckCast" <+> pretty cn
  pretty (Invoke mn i)    = text "GetField" <+> pretty mn <+> int i
  pretty Return           = text "Return"
  pretty Pop              = text "Pop"
  pretty IAdd             = text "IAdd"
  pretty ICmpGeq          = text "CmpGeq"
  pretty (Goto i)         = text "Goto" <+> int i
  pretty CmpEq            = text "CmpEq"
  pretty CmpNeq           = text "CmpNeq"
  pretty (IfFalse i)      = text "IfFalse" <+> int i
  pretty ISub             = text "ISub"
  pretty BNot             = text "Not"
  pretty BAnd             = text "And"
  pretty BOr              = text "Or"

instance Pretty Program where
  pretty p = vsep prettyClasses
    where 
      cs = case p of P cs' -> M.elems cs'
      prettyClasses = map pretty cs

