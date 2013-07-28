-- | This module provides the abstract value.
module Jat.PState.AbstrValue
  (
    Address
  , AbstrValue (..)
  , typeOf
  , theAddress
  , abstract
  , defaultValue
  )
where

import Jat.PState.AbstrDomain
import Jat.PState.BoolDomain
import Jat.PState.IntDomain
import Jat.Utils.Pretty
import qualified Jat.Program as P

-- | Representation of an address.
type Address = Int

-- | The abstract variants of a Jinja Value, where i is a suitably 'IntDomain'.
data AbstrValue i = 
    BoolVal BoolDomain
  | IntVal i
  | RefVal Address
  | Null
  | Unit
  deriving (Show,Eq,Ord)

typeOf :: AbstrValue i -> Maybe P.Type
typeOf (BoolVal _) = Just P.BoolType
typeOf (IntVal _)  = Just P.IntType
typeOf (RefVal _)  = Nothing
typeOf Null        = Just P.NullType
typeOf Unit        = Just P.Void

-- | Returns the address of a 'RefVal'.
-- Returns an error if its not an address.
theAddress :: AbstrValue i -> Address
theAddress (RefVal a) = a
theAddress _ = error "Jat.PState.AbstractValue.theAddress: not an address"

-- | Transforms a value in an abstract value.
abstract :: (IntDomain i) => P.Value -> AbstrValue i
abstract val = case val of
  P.BoolVal b -> BoolVal $ constant b
  P.IntVal i  -> IntVal $ constant i
  P.Null      -> Null
  P.Unit      -> Unit
  _           -> error "assert: Jat.PState.AbstrValue.abstract: illegal use of address."

-- | Returns the abstracted default value.
defaultValue :: (IntDomain i) => P.Type -> AbstrValue i
defaultValue = abstract . P.defaultValue

instance Pretty i => Pretty (AbstrValue i) where
  pretty (BoolVal b) = pretty b
  pretty (IntVal i)  = pretty i
  pretty (RefVal a)  = text "x" <> int a
  pretty Null        = string "null"
  pretty Unit        = string "unit"

