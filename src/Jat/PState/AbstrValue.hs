module Jat.PState.AbstrValue
  (
    Address
  , AbstrValue (..)
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

type Address = Int

data AbstrValue i = 
    BoolVal BoolDomain
  | IntVal i
  | RefVal Address
  | Null
  | Unit
  deriving (Show,Eq)

theAddress :: AbstrValue i -> Address
theAddress (RefVal a) = a
theAddress _ = error "Jat.PState.AbstractValue.theAddress: not an address"

abstract :: (IntDomain i) => P.Value -> AbstrValue i
abstract val = case val of
  P.BoolVal b -> BoolVal $ constant b
  P.IntVal i  -> IntVal $ constant i
  P.Null      -> Null
  P.Unit      -> Unit
  _           -> error "assert: Jat.PState.AbstrValue.abstract: illegal use of address."

defaultValue :: (IntDomain i) => P.Type -> AbstrValue i
defaultValue = abstract . P.defaultValue

instance Pretty i => Pretty (AbstrValue i) where
  pretty (BoolVal b) = pretty b
  pretty (IntVal i)  = pretty i
  pretty (RefVal a)  = text "x" <> int a
  pretty Null        = string "null"
  pretty Unit        = string "unit"

