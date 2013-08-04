module Jsat.Reachability where

import Jsat.Data
import Jsat.Utility ((|>))
import qualified Jsat.PairSet as PS
import Jsat.Program as P

import qualified Data.Set as S

data RhVar = RhStkVar !Int | RhLocVar !Int | RhTmpVar !Int | RhOutVar deriving (Show,Eq,Ord)

newtype ReachabilityFact = RhFact (Rh, [RhVar]) deriving (Show,Eq,Ord)
data Rh = Rh (PS.PairSet RhVar) (S.Set RhVar) deriving (Show, Eq, Ord)

index :: [RhVar] -> RhVar
index []             = RhStkVar 0
index (RhStkVar i:_) = RhStkVar (i+1)
index _              = error "Jsat.Reachability.index: illegal stk"

tos :: [RhVar] -> RhVar
tos (RhStkVar i:_) = RhStkVar i
tos _              = error "Jsat.Reachability.tos: illegal stk"

unview :: RhVar -> Var
unview (RhStkVar i) = StkVar i
unview (RhLocVar i) = LocVar i
unview _            = error "Jsat.Reachability.unview: illegal var"

rhFlow :: Flow ReachabilityFact
rhFlow = Flow rhLattice rhTransfer rhQueryV

rhLattice :: SemiLattice ReachabilityFact
rhLattice = SemiLattice rhName rhBot rhJoin
  where
    rhName = "Reachability"
    rhBot  = undefined
    rhJoin = undefined

rhTransfer :: Transfer ReachabilityFact
rhTransfer = Transfer rhTransferf rhSetup rhProject rhExtend
  where
    rhTransferf q p ins (RhFact (rh, stk)) = RhFact $ case ins of
      Load i        -> let k = index stk in ((k `assign` RhLocVar i) q rh, k:stk)
      Store i       -> let k = tos stk   in ((RhLocVar i `assign` k  ) q rh, tail stk)
      Push _        -> push (rh,stk)
      New _         -> push (rh,stk)
      GetField _ _  -> let v = tos stk in 
                      case hasTypeQ q (unview v) of
                        Just (RefType _) -> 
                          let rh' = rh
                                    |> \lrh -> ( [(w,v) | w <- sharesWith v q lrh] `rhinserts` lrh)
                                    |> \lrh -> if v `cymember` lrh then [(v,v)] `rhinserts` lrh else lrh
                          in (rh',stk)
                        _ -> (rh,stk)   
      PutField _ _  -> undefined
      CheckCast _   -> pop (rh,stk)
      Pop           -> pop (rh,stk)
      IAdd          -> push $ pop2 (rh,stk)
      ISub          -> push $ pop2 (rh,stk)
      Goto _        -> (rh,stk)
      IfFalse _     -> pop (rh,stk)
      CmpEq         -> push $ pop2 (rh,stk) 
      CmpNeq        -> push $ pop2 (rh,stk) 
      ICmpGeq       -> push $ pop2 (rh,stk)
      BNot          -> push $ pop (rh,stk)
      BOr           -> push $ pop2 (rh,stk)
      BAnd          -> push $ pop2 (rh,stk)
      Return        -> undefined
      Invoke _ _    -> undefined
    rhSetup     = undefined
    rhProject   = undefined
    rhExtend    = undefined


    sharesWith v q (Rh rh cy) = [ w | w <- vars, v /= w, Just True <- [mayShareQ q (unview v) (unview w)] ]
      where 
        vars = vars1 ++ vars2
        vars1 = [ w | w <- vs1 ++ vs2 ,validVar w ]
          where (vs1,vs2) = unzip $ PS.elems rh
        vars2 = [ w | w <- S.elems cy, validVar w ]

        validVar (RhStkVar _) = True
        validVar (RhLocVar _) = True
        validVar _          = False

    rhinserts rs (Rh rh cy) = Rh (rs `PS.inserts` rh) cy
    cyinserts cs (Rh rh cy) = Rh rh (S.fromList cs `S.union` cy)

    v `assign` w = assign' v w
    assign' v w q rh 
      | v == w                             = error "Reachability.assign: same index"
      | isRefType' (hasTypeQ q (unview w)) = rh' `union` ((v,w) `rename` rh')
      | otherwise                          = rh'
      where 
        rh' = v `delete` rh
        isRefType' (Just ty) = isRefType ty
        isRefType' Nothing   = False


    union (Rh rh1 cy1)  (Rh rh2 cy2) = Rh (rh1 `PS.union` rh2) (cy1 `S.union` cy2)
    delete v (Rh rh cy) = Rh (v `PS.delete'` rh) (v `S.delete` cy)
    rename (v,w) (Rh rh cy) = Rh ([(v,w)] `PS.rename` rh) (S.map (\v' -> if v==v' then w else v') cy)

    cymember v (Rh _ cy) = v `S.member` cy

    pop (rh,k:ks) = (k `delete` rh, ks)
    pop (_ ,[])   = error "assertion error: shFwdTransfer: empty stk"
    pop2 = pop . pop
    push (rh,stk) = (rh,index stk :stk)

rhQueryV :: QueryV ReachabilityFact
rhQueryV = QueryV rhMayShare rhMayAlias rhMayUnpure rhTypeOf
  where
    rhMayShare  = undefined
    rhMayAlias  = undefined
    rhMayUnpure = undefined
    rhTypeOf    = undefined



