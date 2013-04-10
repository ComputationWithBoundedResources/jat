module Jat.PState.Heap 
  (
    Heap

  , emptyH
  , addresses
  , lookupH
  , insertH
  , insertHA
  , deallocate
  , updateH
  , mapValuesH
  , normalizeH

  , paths
  , pathValue
  , pathsFromTo
  , reachable
  , reachableFrom
  , isCyclic
  , hasCommonSuccessor
  , isNotTreeShaped
  , commonPrefix
  , hasCommonPrefix
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
import qualified Data.IntMap as M

type Cell     = Int
type Memory i = M.IntMap (Object i)

data Heap i = Heap Cell (Memory i)

emptyH :: Heap i
emptyH = Heap 1 M.empty

addresses :: Heap i -> [Address]
addresses = M.keys . memory

memory :: Heap i -> Memory i
memory (Heap _ mem) = mem

lookupH :: Address -> Heap i -> Object i
lookupH r hp = errmsg `fromMaybe` M.lookup r (memory hp)
  where errmsg = error "Jat.PState.Object: invalid address"

insertH :: Object i -> Heap i -> Heap i
insertH obj (Heap cnt mem) = Heap (cnt+1) (M.insert cnt obj mem)

insertHA :: Object i -> Heap i -> (Address, Heap i)
insertHA obj (Heap cnt mem) = (cnt,hp) 
  where
    cnt' = cnt+1
    hp   = Heap cnt' (M.insert cnt obj mem)

deallocate :: Address -> Heap i -> Heap i
deallocate = mapMem . M.delete

updateH :: Address -> Object i -> Heap i -> Heap i
updateH r obj = mapMem $ M.insert r obj

mapMem :: (Memory i -> Memory i) -> Heap i -> Heap i
mapMem f (Heap cnt mem) = Heap cnt (f mem)

mapValuesH :: (AbstrValue i -> AbstrValue i) -> Heap i -> Heap i
mapValuesH f = mapMem (fmap (mapValuesO f))

normalizeH :: [Address] -> Heap i -> Heap i
normalizeH as hp = mapMem (M.filterWithKey (\a _ -> a `elem` as')) hp
  where as' = reachables as hp

-- graph functions

paths :: Address -> Heap i -> [[(P.ClassId, P.FieldId)]]
paths adr hp = paths' S.empty (RefVal adr) 
  where
    paths' visited (RefVal r) | r `S.member` visited = [[]]
    paths' visited (RefVal r) =
      case lookupH r hp of
        AbsVar _      -> [[]]
        Instance _ ft -> [] : concatMap unroll (assocsFT ft)
        where 
          unroll (k,v) = [k]:[ k:ls | ls <- filter (not . null) $ paths' visited' v]
          visited' = r `S.insert` visited
    paths' _ _ = [[]]

pathValue :: Address -> [(P.ClassId, P.FieldId)] -> Heap i -> AbstrValue i
pathValue adr [] _            = RefVal adr
pathValue adr [(cn,fn)] hp    = lookupFT cn fn . fieldTable $ lookupH adr hp 
pathValue adr ((cn,fn):ls) hp = case lookupFT cn fn . fieldTable $ lookupH adr hp of
  RefVal adr2 -> pathValue adr2 ls hp
  val         -> val

pathsFromTo :: Eq i => Address -> Address -> Heap i -> [[(P.ClassId, P.FieldId)]]
pathsFromTo adr1 adr2 hp = filter target2 paths1 
  where
    paths1       = paths adr1 hp
    target2 path = RefVal adr2 == pathValue adr1 path hp

commonPrefix :: [(P.ClassId,P.FieldId)] -> [(P.ClassId,P.FieldId)] -> [(P.ClassId,P.FieldId)]
commonPrefix (l1:ls1) (l2:ls2) | l1 == l2 = l1:commonPrefix ls1 ls2
commonPrefix _ _ = []

hasCommonPrefix :: [(P.ClassId,P.FieldId)] -> [(P.ClassId,P.FieldId)] -> Bool
hasCommonPrefix paths1 paths2 = not . null $ commonPrefix paths1 paths2

toGraph :: Heap i -> Gr.Gr () ()
toGraph hp = Gr.mkUGraph (fst $ unzip lnodes) ledges
  where
    lnodes = M.assocs $ memory hp
    ledges = concatMap (\(src,obj) -> map (\trg -> (src,trg)) $ referencesO obj) lnodes

reachable :: Address -> Heap i -> [Address]
reachable adr = reachables [adr]

reachables :: [Address] -> Heap i -> [Address]
reachables adrs hp = concatMap (`Gr.reachable` gr) adrs
  where gr = toGraph hp

reachableFrom :: Address -> Heap i -> [Address]
reachableFrom adr hp = filter (\ladr -> adr `elem` reachable ladr hp) (Gr.nodes . toGraph $ hp)

isCyclic :: Address -> Heap i -> Bool
isCyclic adr hp = any (adr `elem`) $ filter notTrivial $ Gr.scc (toGraph hp)
  where
    notTrivial [_] = False
    notTrivial _   = True

hasCommonSuccessor :: Address -> Heap i -> Bool
hasCommonSuccessor adr hp = anyIntersection $ map (S.fromList . reaches) refs
  where
    refs         = referencesO $ lookupH adr hp
    reaches adr' = reachable adr' hp

isNotTreeShaped :: Address -> Heap i -> Bool
isNotTreeShaped adr hp = isCyclic adr hp || hasCommonSuccessor adr hp 

instance (Pretty i) => Pretty (Heap i) where
  pretty hp = vsep $ prettyMem (memory hp)
    where
      prettyMem m        = map prettyElem $ M.assocs m
      prettyElem (r,obt) = text (show r) <> equals <> pretty obt

