-- | This module provides the type of an (abstract) object.
module Jat.PState.Object
  (
    Object (..)
  , className
  , fieldTable
  , isInstance
  , mapValuesO
  , referencesO

  , FieldTable
  , elemsFT
  , updateFT
  , emptyFT
  , lookupFT
  , assocsFT
  )
where

import Jat.PState.AbstrValue 
import Jat.Utils.Pretty
import qualified Jinja.Program as P

import Data.Char (toLower)
import Data.Maybe (fromMaybe)
import qualified Data.Map as M

-- | A 'FieldTable' maps pairs of class name and field name to abstract values.
type FieldTable i = M.Map (P.ClassId, P.FieldId) (AbstrValue i)

-- | An 'Object' may be a concrete instance or an abstract variable.
data Object i = 
    Instance P.ClassId (FieldTable i)
  | AbsVar P.ClassId
  deriving (Show)

-- | Returns the class name of an object.
className :: Object i -> P.ClassId
className (Instance cn _) = cn
className (AbsVar cn)     = cn

-- | Returns the field table of an object.
fieldTable :: Object i -> FieldTable i
fieldTable (Instance _ ft) = ft
fieldTable _               = error "assert: illegal access to fieldtable"

-- | Checks if the object is an conrete instance.
isInstance :: Object i -> Bool
isInstance (Instance _ _) = True
isInstance _              = False

-- | Maps a value function over the object.
mapValuesO :: (AbstrValue i -> AbstrValue i) -> Object i -> Object i
mapValuesO f (Instance cn ft) = Instance cn (M.map f ft)
mapValuesO _ var = var

-- | Returns the the addresses stored in an 'Object'.
referencesO :: Object i -> [Address]
referencesO (Instance _ ft) = [ ref | RefVal ref <- M.elems ft ]
referencesO (AbsVar _)      = []


-- | Returns an aempty field table.
emptyFT :: FieldTable i
emptyFT = M.empty

-- | Updates a field table.
updateFT :: P.ClassId ->  P.FieldId -> AbstrValue i -> FieldTable i -> FieldTable i
updateFT cn fn = M.insert (cn, fn)

-- | Returns the value of the given field of the field table.
-- Returns an error if the field does not exist.
lookupFT :: P.ClassId -> P.FieldId -> FieldTable i -> AbstrValue i
lookupFT cn fn ft = errmsg `fromMaybe` M.lookup (cn,fn) ft
  where errmsg = error $ "Jat.PState.Object.lookupFT: element not found " ++ show (cn,fn)

-- | Retuns the entries of the field table as pair of identifier and value.
assocsFT :: FieldTable i -> [((P.ClassId,P.FieldId),AbstrValue i)]
assocsFT = M.assocs

-- | Returns the values of the field table.
elemsFT :: FieldTable i -> [AbstrValue i]
elemsFT = M.elems

instance Pretty i => Pretty (Object i) where
  pretty (Instance cn ft) = pretty cn <> encloseSep lparen rparen comma (prettyFT ft)
    where
      prettyFT = map prettyElem . M.toList
      prettyElem ((cne,fne),v) = pretty cne <> dot <> pretty fne <> equals <> pretty v
  pretty (AbsVar cn) = text . map toLower . show $ pretty cn

