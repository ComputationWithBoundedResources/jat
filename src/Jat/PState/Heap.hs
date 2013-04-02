module Jat.PState.Heap 
  (
    Heap

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

data Heap i = Heap Cell (Memory i)

emptyH :: Heap i
emptyH = Heap 0 Gr.empty

memory :: Heap i -> Memory i
memory (Heap _ mem) = mem

lookupH :: Address -> Heap i -> Object i
lookupH r hp = errmsg `fromMaybe` lab (memory hp) r
  where errmsg = error "Jat.PState.Object: invalid address"

insertH :: Object i -> Heap i -> Heap i
insertH obj (Heap cnt mem) = Heap (cnt+1) (insNode (cnt,obj) mem)

insertHA :: Object i -> Heap i -> (Address, Heap i)
insertHA obj (Heap cnt mem) = (cnt,hp) 
  where
    cnt' = cnt+1
    hp   = Heap cnt' (insNode (cnt,obj) mem)


updateH :: Address -> Object i -> Heap i -> Heap i
updateH r obj = mapMem (insNode (r,obj))

mapMem :: (Memory i -> Memory i) -> Heap i -> Heap i
mapMem f (Heap cnt mem) = Heap cnt (f mem)

mapValuesH :: (AbstrValue i -> AbstrValue i) -> Heap i -> Heap i
mapValuesH f = mapMem (nmap (mapValuesO f))

-- graph functions

paths :: Address -> Heap i -> [[(P.ClassId, P.FieldId)]]
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



instance (Pretty i) => Pretty (Heap i) where
  pretty (Heap _ mem) = vsep $ prettyMem mem
    where
      prettyMem = map prettyElem . labNodes
      prettyElem (r,obt) = text (show r) <> equals <> pretty obt

