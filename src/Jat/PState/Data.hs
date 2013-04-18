-- | This module provides the type of a JBC program state.
module Jat.PState.Data 
  (
    PState (..)
  , PException (..)
  , frames
  , frame
  , heap 
  , annotations

  , Path
  , Root (..)
  , RPath(..)
  )
where

import Jat.PState.Frame
import Jat.PState.Heap
import Jat.Utils.Pretty
import qualified Jat.Program as P

-- | The abstract State.
data PState i a  = 
    PState (Heap i) [Frame i] a
  | EState PException 
-- | The program exception.
data PException  = NullPointerException deriving Show


-- | Returns the list of frames.
frames :: PState i a -> [Frame i]
frames (PState _ frms _) = frms
frames (EState _)        = []

-- | Returns the top frame.
frame :: PState i a -> Frame i
frame (PState _ frms _) 
  | null frms = error "Jat.PState.Data.frame: assertion error: empty stack."
  | otherwise = head frms
frame (EState _) = error "Jat.PState.Data.frame assertion error: exceptional state"

-- | Returns the heap.
heap :: PState i a -> Heap i
heap (PState hp _ _) = hp
heap (EState _)      = error "Jat.PState.Data.heap: assertion error: exceptional state"

-- | Returns the annotations.
annotations :: PState i a -> a
annotations (PState _ _ ann) = ann
annotations (EState _)       = error "Jat.PState.Data.annotations: assertion error: exceptional state"

-- | A path in the heap represented by pairs of class and field identifiers.
type Path = [(P.ClassId, P.FieldId)]

-- | A Root origin from the frame.
data Root = RStk Int Int | RLoc Int Int deriving (Eq,Show)

-- | A rooted path.
data RPath= RPath Root Path deriving (Eq)
instance Show RPath where
  show (RPath root path) = show root ++ show (map prettyEdge path)
    where prettyEdge (cn,fn) = pretty cn <> char '.' <> pretty fn <> char '>'

instance (Pretty i, Pretty a) => Show (PState i a) where
  show = show . pretty

instance Pretty PException where
  pretty = text . show

instance (Pretty i, Pretty a) => Pretty (PState i a) where
  pretty (EState ex)          = pretty ex
  pretty (PState hp frms ann) =
    vsep (map pretty frms) <$> pretty hp <$> pretty ann

