-- | Pair Sharing domain following 'Pair Sharing Analysis of Object-Oriented
-- Programs' Spoto et al.
module Jsat.PairSharing where


import Jsat.Utility ((|>))
import Jsat.Data
import Jsat.Program
import qualified Jsat.PairSet as S

import Text.PrettyPrint.ANSI.Leijen ((<+>),(<>))
import qualified Text.PrettyPrint.ANSI.Leijen as P
{-import Debug.Trace-}

-- TODO:
-- normalizing wrt types
-- necessary for getfield, closure ...?


-- pair sharing domain sh:
-- (v1,v2) in sh => v1 and v2 may have a commen descendent
-- (v1,v1) not in sh => v1 is null
-- 
-- sharing happens only in 
-- variable assignments: v := w
--- (w,w) in sh   : sh|-v + (v,w) + if (w,x) in sh then (v,x) in sh
--- otherwise     : sh|-v
-- field    assignments: v := w.f
--- (w,w) in sh : sh|-v + (v,w) + if (w,x) in sh and exists common (static-descendent) type (t(w.f),t(x)) then (v,x) in sh
--- othersise   : sh|-v
-- methods

 
-- moving from denotial to operational semantics
-- we treat operand stack as temporal variables ie. Load i -> l_n := i 
-- v := exp and v.f := exp reduces to v := w and v.f = w

-- local vars are identified by their indices
-- stack vars are treated as temporary variables (loading 
--- kept as stack as ususal
--- identified by a unique negative index
--- only stack vars which are on the stack may occur in sh

data ShVar = ShStkVar !Int | ShLocVar !Int | ShTmpVar !Int Type | ShOutVar deriving (Eq,Ord)

instance Show ShVar where
  show (ShStkVar i)   = "sv" ++ show i
  show (ShLocVar i)   = "lv" ++ show i
  show (ShTmpVar i _) = "tv" ++ show i
  show (ShOutVar  )   = "ov"

newtype SharingFact = ShFact (S.PairSet ShVar, [ShVar])  deriving (Eq,Ord)

instance Show SharingFact where
  show (ShFact (sh,stk)) = show $
    P.string "ShFact" <+> P.lparen 
    <> P.string (show sh) <+> P.char '|' 
    <+> P.string (show stk) <+> P.string "||" <+> P.int (length stk) <> P.rparen


index :: [ShVar] -> ShVar
index []            = ShStkVar 0
index(ShStkVar i:_) = ShStkVar (i+1)
index _             = error "PairSharing.index: invalid stack"

tos :: [ShVar] -> ShVar
tos (ShStkVar i:_) = ShStkVar i
tos _              = error "PairSharing.tos: invalid stack"

view :: Var -> ShVar
view (StkVar i) = ShStkVar i
view (LocVar i) = ShLocVar i

unview :: ShVar -> Var
unview (ShStkVar i) = StkVar i
unview (ShLocVar i) = LocVar i
unview _            = error "PairSharing.unview: illegal variable"


shFlow :: Flow SharingFact
shFlow = Flow shLattice shTransfer shQueryV

shLattice :: SemiLattice SharingFact
shLattice = SemiLattice shName shBot shJoin
  where
    shName = "PairSharing"
    shBot  = ShFact (S.empty,[])
    shJoin _ (ShFact(sh1,stk1)) (ShFact(sh2,stk2)) = ShFact (sh3,stk3)
      where
        sh3 = sh1 `S.union` sh2
        stk3 
          | and $ zipWith (==) stk1 stk2 = stk1 
          | otherwise = error $ "shJoin: invalid variable stk" ++ show (stk1,stk2)


shTransfer :: Transfer SharingFact
shTransfer = Transfer shTransferf shSetup shProject shExtend
  where
    shTransferf p q ins (ShFact (sh, stk)) = ShFact $ case ins of
      Load i -> let k = index stk in ((k `assign` ShLocVar i) sh, k:stk)
      Store i -> case stk of
        []     -> error "assertion error: shTransfer: empty stk"
        (k:ks) -> ((ShLocVar i `assign` k) sh, ks)
      Push _         -> push (sh,stk)
      New _          -> let k = index stk in (k `S.insert'` sh, k:stk)
      GetField _ _   -> normalize p q (sh,stk)
                       {-let -}
                          {-res = index stk -}
                          {-fld = tos stk-}
                       {-in (res `assign` fld) sh |> (fld `S.delete'`) |> (res `mapsto` fld) |> \lsh -> normalize p q (lsh,stk)-}
      PutField _ _   -> case stk of
        (val:ref:_) -> (ref `put` val) sh |> \lsh   -> normalize p q $ pop2 (lsh,stk)
        _            -> error $ "assertion error: shTransfer: illegal stk" ++ show (sh,stk)
      CheckCast _    -> pop (sh,stk)
      Pop            -> pop (sh,stk)
      IAdd           -> push $ pop2 (sh,stk)
      ISub           -> push $ pop2 (sh,stk)
      Goto _         -> (sh,stk)
      IfFalse _      -> pop (sh,stk)
      CmpEq          -> push $ pop2 (sh,stk)
      CmpNeq          -> push $ pop2 (sh,stk)
      ICmpGeq        -> push $ pop2 (sh,stk)
      BNot           -> push $ pop (sh,stk)
      BOr            -> push $ pop2 (sh,stk)
      BAnd           -> push $ pop2 (sh,stk)
      Return         -> undefined
      Invoke _ _     -> undefined

    v `assign` w = assign' v w 
    assign' v1 v2 sh
      | v1 == v2              = error "assertion error: same index"
      | (v2,v2) `S.member` sh = (v1,v2) `S.insert` sh' `S.union` (v2 `mapsto` v1) sh'
      | otherwise             = sh'
      where sh' = v1 `S.delete'` sh

    ref `put` val = put' ref val
    put' ref val sh
      | (ref,ref) `S.member` sh = (ref,val) `S.insert` sh |> S.closure [val] |> (val `S.delete'`) |> S.closure [ref]
      | otherwise = val `S.delete'` sh

    v1 `mapsto` v2 = S.map (\v -> if v == v1 then v2 else v)

    pop (sh,k:ks) = (k `S.delete'` sh, ks)
    pop (_ ,[])   = error "assertion error: shFwdTransfer: empty stk"
    pop2 = pop . pop
    push (sh,stk) = (sh,index stk :stk)

    shSetup p cn mn = ShFact (sh,[])
      where
        md     = theMethod p cn mn
        params = zip [1..] (methodParams md)
        sh     = S.fromList $ (ShLocVar 0, ShLocVar 0)  : [(ShLocVar i, ShLocVar i) | (i, RefType _) <- params]

    shProject _ q _ _ nparams (ShFact (sh, lt)) = ShFact (sh', [])
      where 
        params  = reverse $ take (nparams + 1) lt
        types   = [hasTypeQ q (unview x) | x <- params]
        locals  = [ShLocVar i | i <- [0..nparams]]
        ghosts  = [ShTmpVar i ty | (i,ty) <- zip [0..nparams] types]

        renamer = zip params locals
        sh''    = params `S.restrict` sh |> (renamer `S.rename`) 
        sh'     = foldl (\lsh f -> f lsh) sh'' (zipWith assign ghosts locals)

    shExtend _ _ _ nparams (ShFact (sh1,lt1)) (ShFact (_  ,[])) = ShFact (sh2,lt2)
      where 
        (ps,lt') = splitAt (nparams + 1) lt1
        sh2      = ps `S.deletes'` sh1
        lt2      = index lt' :lt'
      
    shExtend _ q _ nparams (ShFact (sh1,lt1)) (ShFact (sh2,[ShStkVar 0])) = ShFact (sh3,lt3)
      where
        params = reverse $ take (nparams + 1) lt1
        types  = [hasTypeQ q (unview x) | x <- params]
        ghosts = [ShTmpVar i ty | (i,ty) <- zip [0..nparams] types]
        out    = ShStkVar 0

        sh'  = S.restrict (out:ghosts) sh2 |> S.rename  ((ShStkVar 0, ShOutVar) : zip ghosts params)
        sh'' = sh' `S.union` sh1
        sh3  = close sh'' (closef sh'') |> S.deletes' params |> S.rename [(ShOutVar, index lt')]
        lt'  = drop (nparams + 1) lt1
        lt3  = index lt':lt'

        
        close s1 s2 | s1 == s2 = s1
        close s1 s2           = close s2 (closef s1)
        closef s1 = foldl (\lsh (v1,v2) -> [v1,v2] `S.closure` lsh) s1 (S.elems sh') 

    normalize p q (sh,lt) = (S.filter (uncurry $ areSharingTypes' p q) sh,lt)

    areSharingTypes' p q x y = areSharingTypes p (ty x) (ty y)
      where
        ty (ShTmpVar _ t) = t
        ty z              = hasTypeQ q (unview z)


shQueryV :: QueryV SharingFact
shQueryV = defaultQueryV {mayShare = shMayShare}
  where shMayShare (ShFact (sh,_)) x y = Just $ (view x, view y) `S.member` sh



