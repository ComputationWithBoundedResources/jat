module Jat.PState.Heap 
  (
    Heap

  , emptyH
  , addresses
  , lookupH
  , insertH
  , insertHA
  , updateH
  , mapValuesH

  , paths
  , reachable
  , reachableFrom
  , isCyclic
  , hasCommonSuccessor
  , isNotTreeShaped
  )
where


import Jat.PState.AbstrValue
import Jat.PState.Object
import Jat.Utils.Pretty
import Jat.Utils.Fun
import qualified Jat.Program as P

import qualified Data.Graph.Inductive as Gr
import Data.Maybe (fromMaybe)
import qualified Data.Set as S

type Cell   = Int
type Memory i = Gr.Gr (Object i) (P.ClassId, P.FieldId)

data Heap i = Heap Cell (Memory i)

emptyH :: Heap i
emptyH = Heap 0 Gr.empty

addresses :: Heap i -> [Address]
addresses = Gr.nodes . memory

memory :: Heap i -> Memory i
memory (Heap _ mem) = mem

lookupH :: Address -> Heap i -> Object i
lookupH r hp = errmsg `fromMaybe` Gr.lab (memory hp) r
  where errmsg = error "Jat.PState.Object: invalid address"

insertH :: Object i -> Heap i -> Heap i
insertH obj (Heap cnt mem) = Heap (cnt+1) (Gr.insNode (cnt,obj) mem)

insertHA :: Object i -> Heap i -> (Address, Heap i)
insertHA obj (Heap cnt mem) = (cnt,hp) 
  where
    cnt' = cnt+1
    hp   = Heap cnt' (Gr.insNode (cnt,obj) mem)


updateH :: Address -> Object i -> Heap i -> Heap i
updateH r obj = mapMem (Gr.insNode (r,obj))

mapMem :: (Memory i -> Memory i) -> Heap i -> Heap i
mapMem f (Heap cnt mem) = Heap cnt (f mem)

mapValuesH :: (AbstrValue i -> AbstrValue i) -> Heap i -> Heap i
mapValuesH f = mapMem (Gr.nmap (mapValuesO f))

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

reachable :: Address -> Heap i -> [Address]
reachable adr = Gr.reachable adr . memory

reachableFrom :: Address -> Heap i -> [Address]
reachableFrom adr hp = filter (\ladr -> adr `elem` reachable ladr hp) (Gr.nodes . memory $ hp)

isCyclic :: Address -> Heap i -> Bool
isCyclic adr hp = any (adr `elem`) $ Gr.scc (memory hp)

hasCommonSuccessor :: Address -> Heap i -> Bool
hasCommonSuccessor adr hp = anyIntersection $ map (S.fromList . reachables) refs
  where
    refs            = referencesO $ lookupH adr hp
    reachables adr' = reachable adr' hp

isNotTreeShaped :: Address -> Heap i -> Bool
isNotTreeShaped adr hp = isCyclic adr hp || hasCommonSuccessor adr hp 

instance (Pretty i) => Pretty (Heap i) where
  pretty (Heap _ mem) = vsep $ prettyMem mem
    where
      prettyMem = map prettyElem . Gr.labNodes
      prettyElem (r,obt) = text (show r) <> equals <> pretty obt

