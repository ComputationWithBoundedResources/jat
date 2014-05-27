-- | Simple may-alias analysis
module JFlow.PointsTo
  (
    PointsToFact
  , ptFlow
  , mayAlias
  )
where

import Jinja.Program

import JFlow.Data

import qualified Data.Set as S
import Data.Either
import Text.PrettyPrint.ANSI.Leijen hiding (empty)
--import Debug.Trace


data NId =
    ParamId Int
  | PLocId (CallString,PC) deriving (Eq,Ord,Show)

data PtEdge = 
    REdge Var NId
  | NEdge NId (ClassId,FieldId) NId
  deriving(Eq,Ord,Show)

type PtNode = Either Var NId
type PtNodes = S.Set PtNode

nids :: PtNodes -> S.Set NId
nids = S.fold k S.empty
  where
    k (Right n) = S.insert n
    k _         = id

vids :: PtNodes -> S.Set Var
vids = S.fold k S.empty
  where
    k (Left v) = S.insert v
    k _        = id

var :: Var -> PtNode
var = Left

nid :: NId -> PtNode
nid = Right

type PtGr = S.Set PtEdge


empty :: PtGr
empty = S.empty

singleton :: PtEdge -> PtGr
singleton = S.singleton

to :: PtEdge -> PtNode
to (REdge _ n)   = nid n
to (NEdge _ _ n) = nid n

from :: PtEdge -> PtNode
from (REdge v _)   = var v
from (NEdge n _ _) = nid n

edgesTo :: PtNode  -> PtGr -> PtGr
edgesTo n = S.filter ((==n) . to)

edgesFrom :: PtNode -> PtGr -> PtGr
edgesFrom n = S.filter ((==n) . from)

union :: PtGr -> PtGr -> PtGr
union = S.union

minus :: PtGr -> PtGr -> PtGr
minus = S.difference

edges :: PtNode -> PtGr -> PtGr
edges n gr = edgesTo n gr `union` edgesFrom n gr

nodes :: PtNode -> PtGr -> PtNodes
nodes n gr = to `S.map` edgesFrom n gr

nodes' :: PtNode -> (ClassId,FieldId) -> PtGr -> PtNodes
nodes' (Left v) _ _ = S.empty
nodes' (Right n) fn gr = S.foldr k S.empty gr
  where
    k (NEdge n1 fn1 n')
      | n == n1 && fn == fn1 = S.insert (nid n')
      | otherwise            = id
    k _ = id

rename :: (Var -> Var) -> (NId -> NId) -> PtGr -> PtGr
rename f g = S.map k
  where
    k (REdge v n) = REdge (f v) (g n)
    k (NEdge n1 fn n2) = NEdge (g n1) fn (g n2)

newtype PointsToFact = PtFact PtGr deriving (Eq,Ord)

instance MayAliasQ PointsToFact where mayAliasQ = mayAlias


ptmap :: (PtGr -> PtGr) -> PointsToFact -> PointsToFact
ptmap m (PtFact gr) = PtFact (m gr)

mayAlias :: PointsToFact -> Var -> Var -> Bool
mayAlias (PtFact gr) x y = not . S.null $ nodes (var x) gr `S.intersection` nodes (var y) gr

instance Pretty PointsToFact where
  pretty (PtFact gr) = 
    string "PtFact" <$> text (show gr)

instance Show PointsToFact where
  show = show . pretty


ptFlow :: (HasIndexQ w, HasTypeQ w) => Flow PointsToFact w
ptFlow = Flow ptLattice ptTransfer

ptLattice :: SemiLattice PointsToFact
ptLattice = SemiLattice ptName ptBot ptJoin
  where
    ptName = "PointsTo"
    ptBot  = PtFact empty
    ptJoin _ (PtFact pt1) (PtFact pt2) = PtFact $ pt1 `union` pt2

ptTransfer :: (HasIndexQ w, HasTypeQ w) => Transfer PointsToFact w
ptTransfer = Transfer ptTransferf ptSetup ptProject ptExtend
  where

    -- x = y
    assign :: Var -> Var -> PtGr -> PtGr
    assign x y pt = (pt `minus` kill) `union` gen
      where
        kill = edges (var x) pt
        gen  = REdge x `S.map` nids (nodes (var y) pt)

    -- x = x.f
    load :: Var -> (ClassId,FieldId) -> Type -> PtGr -> PtGr
    load x fn ft pt = (pt `minus` kill) `union` gen
      where
        kill = edges (var x) pt
        gen
          | isPrimitiveType ft = empty
          | otherwise          = REdge x `S.map` nids si
        si   = S.fold k S.empty (nodes (var x) pt)
        k n acc = nodes' n fn pt `S.union` acc
        
    -- ref.f = val
    store x fn ft y pt = pt `union` gen
      where
        gen 
          | isPrimitiveType ft = S.empty
          | otherwise          = S.fromList $ [NEdge n1 fn n2 | n1 <- n1s, n2 <- n2s]
        n1s = S.toList . nids $ nodes (var x) pt
        n2s = S.toList . nids $ nodes (var y) pt

    -- x = new c
    new x n pt = (pt `minus` kill) `union` gen
      where
        kill = edges (var x) pt
        gen = singleton (REdge x n)
        


    -- index (i,j) after operation
    ptTransferf p ploc ins (_,w) gr =
      let (i,j) = hasIndexQ w in ptTransferf' p ploc ins w gr i j
    ptTransferf' p ploc ins w (PtFact gr) i j = PtFact $ case ins of
      Load n          -> (StkVar i j `assign` LocVar i n) gr
      Store n         -> let (x,y) = (LocVar i n, StkVar i (j+1)) in (x `assign` y) gr
      Push _          -> gr 
      New _           -> let x = StkVar i j in new x (PLocId ploc) gr
      GetField fn cn  -> let x = StkVar i j in load x (cn,fn) (snd $ field p cn fn) gr
      PutField fn cn  -> let (val,ref) = (StkVar i (j+2), StkVar i (j+1)) in store ref (cn,fn) (snd $ field p cn fn) val gr
      CheckCast _     -> gr
      Pop             -> let x = StkVar i (j+1) in gr `minus` edges (var x) gr
      IAdd            -> gr
      ISub            -> gr
      Goto _          -> gr
      IfFalse _       -> gr
      CmpEq           -> let (x,y) = (StkVar i (j+1), StkVar i j) in (gr `minus` edges (var x) gr) `minus` edges (var y) gr
      CmpNeq          -> let (x,y) = (StkVar i (j+1), StkVar i j) in (gr `minus` edges (var x) gr) `minus` edges (var y) gr
      ICmpGeq         -> gr
      BNot            -> gr
      BOr             -> gr
      BAnd            -> gr
      Return          -> undefined
      Invoke _ _      -> undefined


    ptSetup p cn mn = PtFact (S.fromList gr)
      where
        md     = theMethod p cn mn
        params = zip [1..] (methodParams md)
        gr     = REdge (LocVar 0 0) (ParamId 0) : [REdge (LocVar 0 i) (ParamId i) | (i, RefType _) <- params]

    ptProject _ _ _ nparams w (PtFact gr) = PtFact (rename k id gr)
      where
        (i,j) = hasIndexQ w
        table = zip [StkVar i k | k <- [j,j-1..]] [LocVar (i+1) k | k <- [nparams,nparams-1..0]]
        k x   = maybe x id (lookup x table)

    ptExtend _ _ nparams w _ (PtFact gr) =
      PtFact $ S.filter k2 ((rl `assign` rs) gr)
      where
        (i,j) = hasIndexQ w
        (rs,rl) = (StkVar (i+1) 0, StkVar i (j -nparams))
        k (StkVar i2 _) = i2 <= i
        k (LocVar i2 _) = i2 <= i
        k2 (REdge x _) = k x
        k2 _           = True
  

