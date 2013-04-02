module Jat.PState.Data where

import Jat.PState.Frame
import Jat.PState.Heap
import Jat.Utils.Pretty

data PState i a  = 
    PState (Heap i a) [Frame i]
  | EState PException 
data PException  = NullPointerException deriving Show


frames :: PState i a -> [Frame i]
frames (PState _ frms) = frms
frames (EState _) = []

heap :: PState i a -> Heap i a
heap (PState hp _) = hp
heap (EState _)    = error "Jat.PState.Data.heap: assertion error: exceptional state"

frame :: PState i a -> Frame i
frame (PState _ frms) 
  | null frms = error "Jat.PState.Data.frame: assertion error: empty stack."
  | otherwise = head frms
frame (EState _) = error "Jat.PState.Data.frame assertion error: exceptional state"

instance (Pretty i, Pretty a) => Show (PState i a) where
  show = show . pretty

instance Pretty PException where
  pretty = text . show

instance (Pretty i, Pretty a) => Pretty (PState i a) where
  pretty (EState ex)       = pretty ex
  pretty (PState mem frms) =
    vsep (map pretty frms) <$> pretty mem

