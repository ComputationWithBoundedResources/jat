module Jat.PState.Heap 
  (
    Heap
  , annotations
  , mapAnnotations

  , emptyH
  , lookupH
  , insertH
  , insertHA
  , updateH
  , mapValuesH

  , paths
  )
where


import Jat.PState.AbstrValue
import Jat.PState.Object
import Jat.Utils.Pretty
import qualified Jat.Program as P

import Data.Graph.Inductive as Gr
import Data.Maybe (fromMaybe)
import qualified Data.Set as S

type Cell   = Int
type Memory i = Gr (Object i) (P.ClassId, P.FieldId)

data Heap i a = Heap Cell (Memory i) a

emptyH :: a -> Heap i a
emptyH = Heap 0 Gr.empty

memory :: Heap i a -> Memory i
memory (Heap _ mem _) = mem

annotations :: Heap i a -> a
annotations (Heap _ _ a) = a

mapAnnotations :: (a -> a) -> Heap i a -> Heap i a
mapAnnotations f (Heap cnt mem ann) = Heap cnt mem (f ann)

lookupH :: Address -> Heap i a -> Object i
lookupH r hp = errmsg `fromMaybe` lab (memory hp) r
  where errmsg = error "Jat.PState.Object: invalid address"

insertH :: Object i -> Heap i a -> Heap i a
insertH obj (Heap cnt mem ann) = Heap (cnt+1) (insNode (cnt,obj) mem) ann

insertHA :: Object i -> Heap i a -> (Address, Heap i a)
insertHA obj (Heap cnt mem ann) = (cnt,hp) 
  where
    cnt' = cnt+1
    hp   = Heap cnt' (insNode (cnt,obj) mem) ann


updateH :: Address -> Object i -> Heap i a -> Heap i a
updateH r obj = mapMem (insNode (r,obj))

mapMem :: (Memory i -> Memory i) -> Heap i a -> Heap i a
mapMem f (Heap cnt mem ann) = Heap cnt (f mem) ann

mapValuesH :: (AbstrValue i -> AbstrValue i) -> Heap i a -> Heap i a
mapValuesH f = mapMem (nmap (mapValuesO f))

-- graph functions

paths :: Address -> Heap i a -> [[(P.ClassId, P.FieldId)]]
paths adr hp = paths' S.empty (RefVal adr) 
  where
    paths' visited (RefVal r) | r `S.member` visited = [[]]
    paths' visited (RefVal r) =
      case lookupH r hp of
        AbsVar _      -> [[]]
        Instance _ ft -> concatMap unroll (assocsFT ft)
        where 
          unroll (k,v) = [k]:[ k:ls | ls <- filter (not . null) $ paths' visited' v]
          visited' = r `S.insert` visited
    paths' _ _ = [[]]





instance (Pretty i, Pretty a) => Pretty (Heap i a) where
  pretty (Heap _ mem ann) = (vsep $ prettyMem mem) <$> pretty ann
    where
      prettyMem = map prettyElem . labNodes
      prettyElem (r,obt) = text (show r) <> equals <> pretty obt
