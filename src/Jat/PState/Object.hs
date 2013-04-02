module Jat.PState.Object
  (
    Object (..)
  , className
  , fieldTable
  , isInstance
  , mapValuesO
  , referencesO

  , FieldTable
  --, elemsFT
  , updateFT
  , emptyFT
  , lookupFT
  , assocsFT
  )
where

import Jat.PState.AbstrValue 
import qualified Jat.Program as P
import Jat.Utils.Pretty

import Data.Maybe (fromMaybe)
import Data.Char (toLower)
import qualified Data.Map as M

type FieldTable i = M.Map (P.ClassId, P.FieldId) (AbstrValue i)

data Object i = 
    Instance P.ClassId (FieldTable i)
  | AbsVar P.ClassId
  deriving (Show)

className :: Object i -> P.ClassId
className (Instance cn _) = cn
className (AbsVar cn)     = cn

fieldTable :: Object i -> FieldTable i
fieldTable (Instance _ ft) = ft
fieldTable _               = error "assert: illegal access to fieldtable"

isInstance :: Object i -> Bool
isInstance (Instance _ _) = True
isInstance _              = False

mapValuesO :: (AbstrValue i -> AbstrValue i) -> Object i -> Object i
mapValuesO f (Instance cn ft) = Instance cn (M.map f ft)
mapValuesO _ var = var

referencesO :: Object i -> [Address]
referencesO (Instance _ ft) = [ ref | RefVal ref <- M.elems ft ]
referencesO (AbsVar _)      = []

emptyFT :: FieldTable i
emptyFT = M.empty

updateFT :: P.ClassId ->  P.FieldId -> AbstrValue i -> FieldTable i -> FieldTable i
updateFT cn fn = M.insert (cn, fn)

lookupFT :: P.ClassId -> P.FieldId -> FieldTable i -> AbstrValue i
lookupFT cn fn ft = errmsg `fromMaybe` M.lookup (cn,fn) ft
  where errmsg = error $ "Jat.PState.Object.lookupFT: element not found " ++ show (cn,fn)

assocsFT :: FieldTable i -> [((P.ClassId,P.FieldId),AbstrValue i)]
assocsFT = M.assocs

--keysFT :: FieldTable i -> [(P.ClassId, P.FieldId)]
--keysFT = M.keys

--elemsFT :: FieldTable i -> [AbstrValue i]
--elemsFT = M.elems

--referencesFT :: FieldTable i -> [Address]
--referencesFT ft = [ q | RefVal q <- M.elems ft ]



instance Pretty i => Pretty (Object i) where
  pretty (Instance cn ft) = pretty cn <> encloseSep lparen rparen comma (prettyFT ft)
    where
      prettyFT = map prettyElem . M.toList
      prettyElem ((cne,fne),v) = pretty cne <> dot <> pretty fne <> equals <> pretty v
  pretty (AbsVar cn) = text $ map toLower $ show cn
