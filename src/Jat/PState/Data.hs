module Jat.PState.Data where

import Jat.PState.Frame
{-import Jat.PState.Heap-}
import Jat.Utils.Pretty

type Heap a = a

data PState i a  = 
    PState (Heap a) [Frame i]
  | EState PException 
data PException  = NullPointerException deriving Show

instance (Pretty i, Pretty a) => Show (PState i a) where
  show = show . pretty

instance Pretty PException where
  pretty = text . show

instance (Pretty i, Pretty a) => Pretty (PState i a) where
  pretty (EState ex)       = pretty ex
  pretty (PState mem frms) =
    vsep (map pretty frms) <$> pretty mem

