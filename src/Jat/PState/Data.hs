module Jat.PState.Data where

import Jat.PState.Frame
import Jat.PState.Heap
import Jat.Utils.Pretty
import qualified Jat.Program as P

data PState i a  = 
    PState (Heap i) [Frame i] a
  | EState PException 
data PException  = NullPointerException deriving Show


frames :: PState i a -> [Frame i]
frames (PState _ frms _) = frms
frames (EState _)        = []

frame :: PState i a -> Frame i
frame (PState _ frms _) 
  | null frms = error "Jat.PState.Data.frame: assertion error: empty stack."
  | otherwise = head frms
frame (EState _) = error "Jat.PState.Data.frame assertion error: exceptional state"

heap :: PState i a -> Heap i
heap (PState hp _ _) = hp
heap (EState _)      = error "Jat.PState.Data.heap: assertion error: exceptional state"

annotations :: PState i a -> a
annotations (PState _ _ ann) = ann
annotations (EState _)       = error "Jat.PState.Data.annotations: assertion error: exceptional state"

type Path = [(P.ClassId, P.FieldId)]
data Root = RStk Int Int | RLoc Int Int deriving (Eq,Show)
data RPath= RPath Root Path deriving (Eq,Show)

instance (Pretty i, Pretty a) => Show (PState i a) where
  show = show . pretty

instance Pretty PException where
  pretty = text . show

instance (Pretty i, Pretty a) => Pretty (PState i a) where
  pretty (EState ex)          = pretty ex
  pretty (PState hp frms ann) =
    vsep (map pretty frms) <$> pretty hp <$> pretty ann

