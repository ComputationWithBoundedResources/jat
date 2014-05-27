{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- | This module provides functionality for constrained Term rewrite systems (cTRS).
module Jat.Utils.TRS
  (
    prettyTRS
  , prettyITRS
  , prettyCTRS
  , toITRS
  , toCTRS
  
  , simplifyTRS
  , simplifyRHS
  , normaliseCTRS
  )

where

import Jat.CompGraph
import Jat.Utils.Pretty
import qualified Jat.Constraints as PA

import qualified Data.Rewriting.Rule as R
import qualified Data.Rewriting.Rules as RS
import qualified Data.Rewriting.Term as T
import qualified Data.Rewriting.Substitution as S
import qualified Data.Rewriting.Substitution.Type as ST

import Data.List as L
import Data.Char as C
import Data.Maybe (fromMaybe, catMaybes)
import Control.Monad (liftM)
import qualified Data.Graph.Inductive as Gr
import qualified Data.Set as S
import qualified Data.Map as M

--import Debug.Trace

prettyITRS = undefined
toITRS = undefined
simplifyRHS = id
normaliseCTRS = undefined

type PARule = (R.Rule PA.PAFun PA.PAVar, [PA.PATerm])

prettyRule :: (R.Rule PA.PAFun PA.PAVar) -> Doc
prettyRule (R.Rule l r) = hang 2 $ PA.prettyPATerm l <+> text "->" <+> PA.prettyPATerm r

prettyPARule :: PARule -> Doc
prettyPARule (r,[]) = prettyRule r
prettyPARule (r,cs) = prettyRule r <+> text "<==" <+> pts
  where pts = encloseSep lbracket rbracket comma [PA.prettyPATerm c | c <- cs]

rvars ::  PARule -> [PA.PAVar]
rvars (r,cs) = R.vars r ++ concatMap T.vars cs

rmap :: (f -> f')-> (v -> v')-> (R.Rule f v, [T.Term f v])-> (R.Rule f' v', [T.Term f' v'])
rmap f g (R.Rule l r, cs) = (R.Rule (T.map f g l) (T.map f g r), map (T.map f g) cs)

rmap' :: (f -> f')-> (v -> v')-> R.Rule f v -> R.Rule f' v'
rmap' f g (R.Rule l r) = R.Rule (T.map f g l) (T.map f g r)



header :: [PARule] -> Doc
header rules =
  lparen <> text "VAR" <+> prettyvars (allvars rules) <> rparen
  <$> lparen <> text "RULES"
  where
    prettyvars = cat . punctuate space . map (PA.prettyPATerm . T.Var)
    allvars    = S.toList . foldl (\s -> S.union s . S.fromList . rvars) S.empty

footer :: Doc
footer = rparen

{-simplifyTRS :: JGraph i a -> [PARule] -> [PARule]-}
{-simplifyTRS gr rs | trace "simp" False = undefined-}
{-[>simplifyTRS gr rs = combination [] . concatMap (combination es) $ rcomps cs<]-}
{-simplifyTRS gr rs = combination [] . concatMap (combination es) $ rcomps cs-}
  {-where-}
    {-(es,cs) = (\(x,y) -> (map tof x, map (map tof) y)) $ components gr-}
    {-rcomps = map (\ns -> filter (\(r,_) -> root (R.lhs r) `elem` ns) rs)-}
    {-tof i = PA.UFun ('f':show i)-}


components :: JGraph i a -> ([Gr.Node], [[Gr.Node]])
components gr = (map head sccs, sccs ++ Gr.components (Gr.delNodes (concat sccs) gr))
  where
    sccs  = filter k $ Gr.scc gr
    k [n] = n `elem` Gr.suc gr n
    k _   = True

root :: T.Term f v -> f
root (R.Fun f _) = f
root (R.Var _)   = error "simplify.root: unexpected variable"

simplifyTRS :: JGraph i a -> [PARule] -> [PARule]
simplifyTRS gr = combination (map toF . reverse . filter isSimple $ Gr.topsort gr)
{-simplifyTRS gr = combination (map toF . reverse $ Gr.topsort gr)-}
  where
    toF i      = PA.UFun ('f':show i)
    isSimple i = not $ any (>i) $ Gr.pre gr i

combination :: [PA.PAFun] -> [PARule] -> [PARule]
--combination fs rules | trace (show ("combination", fs, length rules)) False = undefined
combination fs rules = foldl (clean) rules fs
  where
    clean rs f
      | True
        && null (tof `intersect` fot)
        && not (null tof)
        && not (null fot)
        && all regular tof
        = cleanF tof fot rs
      | otherwise = rs
      where
        tof = toF f rs
        fot = foT f rs

    funs rs = nub $ map (\(r,_) -> root (R.lhs r)) rs
    regular (r,cs) = all (`elem` T.vars (R.lhs r) ++ concatMap T.vars cs) (T.vars (R.rhs r))
    toF f = filter k where k (r,_) = root (R.rhs r) == f
    foT f = filter k where k (r,_) = root (R.lhs r) == f

    --cleanF tof fot rules | trace (show (length tof,length fot,length rules)) False = undefined
    cleanF tof fot rules = rules `fromMaybe` (((rules \\ (tof ++ fot)) ++) `liftM` combineAll tof fot)
    

    combineAll :: [PARule] -> [PARule] -> Maybe [PARule]
    {-combineAll rs1 rs2 = sequence $ [combine r1 r2 | r1 <- rs1, r2 <- rs2]-}
    combineAll rs1 rs2 = Just [r | Just r <- [combine r1 r2 | r1 <- rs1, r2 <- rs2]]

    combine :: PARule -> PARule -> Maybe PARule
    combine (R.Rule l1 r1,cs1) (R.Rule l2 r2, []) 
      | r1 == l2 = Just (R.Rule l1 r2, cs1)
    combine s t = do
      let 
        (R.Rule l1 r1, c1) = rmap id Left s
        (R.Rule l2 r2, c2) = rmap id Right t
      mu <- mgu r1 l2
      let
        l3 = substitutevars mu l1
        r3 = substitutevars mu r2
        c3 = (substitutevars mu `fmap` c1) ++ (substitutevars mu `fmap` c2)
      return $ normalizevars (R.Rule l3 r3, c3)

    normalizevars (R.Rule l r, cs) =
      let 
        (ml,il,l') = norm (M.empty,0,l)
        (mr,ir,r') = norm (ml,il,r)
        (_,_,cs')  = norms (mr,ir,cs)
      in (R.Rule l' r', cs')
      where
        norm (m,i,(T.Var v)) = case v `M.lookup` m of
          Just v' -> (m,i,T.Var v')
          Nothing -> (M.insert v v' m, i+1, T.Var v')
            where v' = PA.vmap (const i) (fromEither v)
        norm (m,i,T.Fun f ts) = (m', i', T.Fun f ts') where
          (m',i',ts') = norms (m,i,ts)
        norms (m,i,ts) = foldr k (m,i,[]) ts
          where k t (n,j,ss) = let (n',j',t') = norm (n,j,t) in (n',j',t':ss)
        fromEither (Left v) = v
        fromEither (Right v) = v

toCTRS :: JGraph i a -> [PARule] -> [PARule]
toCTRS gr = id
  . L.nub
  . map normalise
  . concatMap expandEq
  . map nfilterTop
  . filter unknownSat
  . map flattenAnd
  . concatMap toDNF
  . map toConstraints
  . concatMap instantiateBVar
  . map substituteBVar
  . simplifyTRS gr
  . map substituteIFun
  where
    apply  sigma r      = (R.Rule (sigma $ R.lhs r) (sigma $ R.rhs r))
    apply' sigma (r,cs) = ((R.Rule (sigma $ R.lhs r) (sigma $ R.rhs r)), map sigma cs)
    singleton (T.Var v) t = S.apply . ST.fromMap $ M.insert v t M.empty
    -- f(x) -> f(x')[x'=x+1] --> f(x) -> f(x+1)
    substituteIFun cr@(r,[]) = cr
    substituteIFun cr@(r,[T.Fun PA.Ass [v, t]])
      | PA.isVar v && PA.isIFun t = (apply (singleton v t) r, [])
      | otherwise   = cr
    substituteIFun _ = error "substituteIFun: unexpected rule"
    -- [b1 = f1, b2 = b1 && f] --> [b2 = f1 && f2]
    substituteBVar  cr@(r,cs) = substituteBVar' (r,[]) cs
    substituteBVar' (r,cs) [] = (r,reverse cs)
    substituteBVar' (r,cs) (d@(T.Fun PA.Ass [v@(T.Var w),t]):ds)
      | PA.isBVar v 
        && PA.isRFun t 
        && w `L.notElem` R.vars r = substituteBVar' (r,cs) (map sigma ds)
      | otherwise                 = substituteBVar' (r,d:cs) ds
      where sigma = singleton v t
    substituteBVar' (r,cs) (d:ds) = substituteBVar' (r,d:cs) ds
    -- [b1 = f] --> [True = f], [False = f]
    instantiateBVar cr@(r,cs) = [apply' (mkMap m) cr | m <- maps bvars]
      where 
        bvars = foldr k [] cs
        k d@(T.Fun PA.Ass [v@(T.Var w),t])
          | PA.isBVar v = (w:)
          | otherwise   = id
        k _             = id
        maps bs = sequence $ map (\v -> [(v,PA.top), (v,PA.bot)]) bs
        mkMap   = S.apply . ST.fromMap . M.fromList
    unknownSat (r,cs) = not $ any (PA.isBot) cs
    toConstraints (r,cs) = (r, map k cs)
      where 
        k d@(T.Fun PA.Ass [b,t]) 
          | PA.isTop b = t
          | PA.isBot b = PA.not t
          | otherwise = d
        k d = d
    toDNF :: PARule -> [PARule]
    toDNF (r,cs) = [(r,cs') | T.Fun PA.And cs' <- css ]
      where css = PA.toDNF (T.Fun PA.And cs)
    nfilterTop (r,cs) = (r,filter (not . PA.isTop) cs)
    flattenAnd (r,cs) = (r,concatMap k cs)
      where 
        k (T.Fun PA.And ts) = concatMap k ts
        k t = [t]
    expandEq (r,cs) = [(r,cs') | cs' <- sequence (map k cs)]
      where
        k (T.Fun PA.Eq [t1,t2])  = [T.Fun PA.Gte[t1,t2], T.Fun PA.Lte [t1,t2]]
        k (T.Fun PA.Neq [t1,t2]) = [T.Fun PA.Gt [t1,t2], T.Fun PA.Lt [t1,t2]]
        k t                      = [t]
    normalise (r,cs) = (r,map PA.normalise cs)

{-toCTRS :: [PARule] -> [PARule]-}
{-toCTRS = id-}
  {-. map instantiateBVal'-}
  {-. map evaluate-}
  {-. map instantiateBVar-}
  {-. concatMap flattenOr-}
  {-. map flattenAnd-}
  {-. map pushNot-}
  {-. map substituteBVal -}
  {-. map substituteRFun -}
  {-. map substituteIFun-}
  {-where -}
    {-substituteIFun (r,cs) = k (r,[]) cs where-}
      {-k (r,ncs) (c@(T.Fun PA.Ass [T.Var v, t@(T.Fun f _)]) :cs)-}
        {-| PA.isIFun f = k (R.Rule (sigma (R.lhs r)) (sigma (R.rhs r)), map sigma ncs) (map sigma cs)-}
        {-where sigma = S.apply (ST.fromMap (M.insert v t M.empty))-}
      {-k (r,ncs) (c:cs) = k (r,c:ncs) cs-}
      {-k (r,ncs) [] = (r,ncs)-}
    {-substituteRFun (r,cs) = (r,k [] cs) where-}
      {-k ncs (c@(T.Fun PA.Ass [T.Var v, t@(T.Fun f _)]) :cs)-}
        {-| PA.isRFun f = k (map sigma ncs) (map sigma cs)-}
        {-where sigma = S.apply (ST.fromMap (M.insert v t M.empty))-}
      {-k ncs (c:cs) = k (c:ncs) cs-}
      {-k ncs [] = ncs-}
    {-substituteBVal (r,cs) = (r,map k cs) where-}
      {-k c@(T.Fun PA.Ass [T.Fun (PA.BConst b) [], t])-}
        {-| b = t-}
        {-| otherwise = PA.not t-}
      {-k c = c-}
    {-pushNot (r,cs) = (r, map PA.pushNot cs)-}
    {-flattenAnd (r,cs) = (r,concatMap k cs) where-}
      {-k c@(T.Fun PA.And ts) = concatMap k ts-}
      {-k c = [c] -}
    {-flattenOr' (r,cs) = (r,concatMap k cs) where-}
      {-k c@(T.Fun PA.And ts) = concatMap k ts-}
      {-k c = [c] -}
    {-flattenOr (r,cs) = zip (cycle [r]) $ foldr k [[]] cs' where-}
      {-k c@(T.Fun PA.Or ts) css = map (\t -> concatMap (t:) css) ts-}
      {-k c css = map (c:) css-}
      {-(_, cs') = flattenOr' (r,cs)-}
    {-instantiateBVar (r,cs) = k (r,[]) cs where-}
      {-k (R.Rule l r, ncs) (T.Var v@(PA.BVar _ _) :cs)  = k (R.Rule (sigma l) (sigma r), map sigma ncs) (map sigma cs)-}
        {-where sigma = S.apply (ST.fromMap (M.insert v PA.top M.empty))-}
      {-k (R.Rule l r, ncs) (T.Fun PA.Not [T.Var v@(PA.BVar _ _)] :cs)  = k (R.Rule (sigma l) (sigma r), map sigma ncs) (map sigma cs)-}
        {-where sigma = S.apply (ST.fromMap (M.insert v PA.bot M.empty))-}
      {-k (r,ncs) (c:cs) = k (r,c:ncs) cs-}
      {-k (r,ncs) [] = (r,ncs)-}
    {-evaluate (r,cs) = (r, map k cs) where-}
      {-k (T.Fun PA.Ass [t1,t2]) = T.Fun PA.Ass [t1, PA.pushNot t2]-}
      {-k c                      = c-}
    {-instantiateBVal' (r,cs) = k (r,[]) cs where-}
      {-k (R.Rule l r, ncs) (T.Fun PA.Ass [T.Var v@(PA.BVar _ _), T.Fun (PA.BConst b) []] :cs) -}
        {-| b         = k (R.Rule (sigmat l) (sigmat r), map sigmat ncs) (map sigmat cs)-}
        {-| otherwise = k (R.Rule (sigmab l) (sigmab r), map sigmab ncs) (map sigmab cs)-}
        {-where-}
          {-sigmat = S.apply (ST.fromMap (M.insert v PA.top M.empty))-}
          {-sigmab = S.apply (ST.fromMap (M.insert v PA.bot M.empty))-}
      {-k (r,ncs) (T.Fun PA.Ass [T.Var v, t] :cs) = k (r,ncs) cs-}
      {-k (r,ncs) (c:cs) = k (r,c:ncs) cs-}
      {-k (r,ncs) []     = (r,ncs)-}



prettyCTRS :: [PARule] -> Doc
prettyCTRS crules =
  header crules
  <$> vsep (map prettyCTRSRule crules)
  <$> footer

prettyCTRSRule :: PARule -> Doc
prettyCTRSRule (R.Rule l r,[]) = prettyCTRSTerm l <+> text "->" <+> prettyCTRSTerm r
prettyCTRSRule (R.Rule l r,cs) = prettyCTRSTerm l <+> text "->" <+> prettyCTRSTerm r <+> text "<=" <+> pts
  where pts = text "@and" <> encloseSep lparen rparen comma [prettyCTRSTerm c | c <- cs]

prettyCTRSTerm :: PA.PATerm -> Doc
prettyCTRSTerm (T.Fun f ts) = case f of
  PA.UFun s -> text s <> args ts where
  PA.IConst i -> char '@' <> int i <> parens empty
  PA.BConst b -> bool b <> parens empty
  PA.Add -> fun "+" ts
  PA.Sub -> fun "-" ts
  PA.Not -> fun "not" ts
  PA.And -> fun "&&" ts
  PA.Or  -> fun "||" ts
  PA.Lt  -> fun "<" ts
  PA.Lte -> fun "=<" ts
  PA.Gte -> fun ">=" ts
  PA.Gt  -> fun ">" ts
  PA.Eq  -> fun "==" ts
  PA.Neq -> fun "/=" ts
  PA.Ass -> fun ":=" ts
  where
    fun s ts = char '@' <> text s <> args ts
    args ts = encloseSep lparen rparen comma [prettyCTRSTerm ti | ti <- ts]
prettyCTRSTerm (T.Var v) = case v of
  PA.UVar s i -> text s <> int i
  PA.IVar s i -> char 'i' <> text s <> int i
  PA.BVar s i -> char 'b' <> text s <> int i

  






    
mgu :: (Eq f, Ord v) => R.Term f v -> R.Term f v -> Maybe (S.Subst f v)
mgu l = S.unifyRef l

substitutevars :: (Eq f, Ord v) => S.Subst f v => T.Term f v -> T.Term f v
substitutevars s = S.apply s


-- mgu
{-type Substitution a b = R.Term a b -> R.Term a b-}

{-maptvars :: (R.Term a b-> R.Term a b) -> R.Term a b -> R.Term a b-}
{-maptvars f (R.Fun a ts)  = R.Fun a (map (maptvars f) ts)-}
{-maptvars f v           = f v-}

{-substitutevars :: Substitution a b -> R.Term a b -> R.Term a b-}
{-substitutevars = maptvars-}

{-emptysubstitution :: Substitution a b-}
{-emptysubstitution = id-}

{-compose :: Substitution a b -> Substitution a b -> Substitution a b-}
{-compose sigma tau = tau . sigma-}

{-mgu :: R.Term a b -> R.Term a b -> Maybe (Substitution a b)-}
{-mgu t1 t2 = unifyterms [t1] [t2]-}

{-unifyterms :: [R.Term a b] -> [R.Term a b] -> Maybe (Substitution a b)-}
{-unifyterms = unifyts (Just emptysubstitution)-}
  {-where-}
    {-unifyt (R.Var x) (R.Var y) | x == y = Just id-}
    {-unifyt (R.Var v1) f      | v1 `elem` T.vars f = Nothing-}
    {-unifyt v1@(R.Var _) f = Just (\t -> if t == v1 then f else t)-}

    {-unifyt f (R.Var y) = unifyt (R.Var y) f-}

    {-unifyt (R.Fun f1 ts1) (R.Fun f2 ts2)-}
      {-| f1 == f2 = unifyts (Just emptysubstitution) ts1 ts2-}
      {-| otherwise = Nothing-}
        
    {-unifyts s0M [] [] = s0M-}
    {-unifyts s0M (t1:ts1) (t2:ts2) = do-}
      {-let subst = substitutevars-}
      {-s0 <- s0M-}
      {-s1 <- unifyt (subst s0 t1) (subst s0 t2)-}
      {-let s2 = return $ compose s0 s1-}
      {-unifyts s2 ts1 ts2-}
    {-unifyts _ ts1 ts2 = error $ "unifyterms: unexpected case: " ++ show (ts1,ts2)-}

{-[>normaliseCTRS :: [CRule] -> [CRule]<]-}
{-[>normaliseCTRS = filter (\(r,c) -> maybe True isNotFalse c) . map (\(r,c) -> (r, C.simplify `liftM` c)) <]-}
  {-[>where isNotFalse c = null [ c | (BConst False) <- [c]]<]-}




{-normaliseCTRS :: [CRule] -> [CRule]-}
{-normaliseCTRS = map mapRule . map mapConstraint -}
  {-where-}
    {-mapRule (R.Rule{R.lhs=l,R.rhs=r},Just c)  = (R.Rule (mapTerm l as) (mapTerm r as), Just $ toConstraints cs)-}
      {-where -}
        {-(as, cs) = L.partition isAssignment $ flatten c-}
        {-toConstraints = unflatten . map k-}
        {-k (Ass (BConst True) c)  = c-}
        {-k (Ass (BConst False) c) = Not (c)-}
        {-k c                      = c-}
    {-mapRule (r,c)                    = (r,c) -}
    {-mapTerm                          = foldl k-}
      {-where k t c' = T.fold (assignment c') R.Fun t-}

    {-isAssignment (Ass (CVar _) _) = True-}
    {-isAssignment _                = False-}
    {-assignment (Ass (CVar v1) c) v2 -}
      {-| v1 == v2  =  op c-}
      {-| otherwise =  R.Var v2-}
    {-assignment c v = R.Var v-}
    {-op (Not c)       = R.Fun "$not" [el c]-}
    {-op (And c d)     = R.Fun "$and" [el c,el d]-}
    {-op (Or  c d)     = R.Fun "$or"  [el c,el d]-}
    {-op (Eq  c d)     = R.Fun "$eq"  [el c,el d]-}
    {-op (Neq c d)     = R.Fun "$neq" [el c,el d]-}
    {-op (Gte c d)     = R.Fun "$gte" [el c,el d]-}
    {-op (Add c d)     = R.Fun "$add" [el c,el d]-}
    {-op (Sub c d)     = R.Fun "$sub" [el c,el d]-}
    {-op e@(BConst _) = el e-}
    {-op _             = error "Jat.Utils.TRS.toITRS: invalid format."-}
    {-el (CVar v)      = R.Var v-}
    {-el (IConst i)    = R.Fun (show i) []-}
    {-el (BConst b)    = R.Fun (show b) []-}
    {-el _             = error "Jat.Utils.TRS.toITRS: invalid format."-}

    {-flatten (c1 `MAnd` c2) = flatten c1 ++ flatten c2-}
    {-flatten c              = [c]-}
    {-unflatten [] = C.top-}
    {-unflatten cs = foldl1 (MAnd) cs-}

    {-mapConstraint (r,c) =  (r, normaliseC r `liftM` c)-}

    {-normaliseC r c = -}
      {-unflatten -}
      {-. filter (/= (BConst True)) -}
      {-. map C.simplify $ update r (flatten c) []-}

    {-update r (c:cs) csnew = case c of-}
      {-(Ass v@(CVar vlit) c') -> update r (map (C.mapvars k) cs) (if vlit `elem` R.vars r then c:csnew else csnew)-}
        {-where k v' = if v == v' then c' else v'-}
      {-c'                -> update r cs (c':csnew)-}
    {-update r [] csnew = reverse csnew-}



{--- simplify according to (refused) RTA2013 paper-}
{-simplifyRHS :: [CRule] -> [CRule]-}
{-simplifyRHS crules = foldl clean crules (funs crules)-}
  {-where-}
    {-clean rules f-}
      {-| null (tof `intersect` fot)-}
        {-[>&& length fot == 1<]-}
        {-&& not (null tof)-}
        {-&& not (null fot)-}
        {-[>&& all nothing fot<]-}
        {-&& all linear tof-}
        {-= cleanF tof fot rules-}
      {-[>| null (tof `intersect` fot) && length fot == 1 = cleanF tof fot rules<]-}
      {-| otherwise = rules-}
      {-where-}
        {-tof = toF f rules-}
        {-fot = foT f rules-}
        {-nothing (_,Nothing) = True-}
        {-nothing _           = False-}
        {-linear (r,c)        = all (`elem` T.vars (R.lhs r) ++ cvars c) (T.vars (R.rhs r))-}
        {-cvars c          = [] `fromMaybe` liftM C.vars c-}

    {-funs rules = nub $ map (\(r,_) -> root (R.lhs r)) rules-}
    {-toF f = filter k where k (r,_) = root (R.rhs r) == f-}
    {-foT f = filter k where k (r,_) = root (R.lhs r) == f-}
    {-cleanF tof fot rules = -}
      {-rules `fromMaybe` ((((rules \\ tof) \\ fot) ++) `liftM` narrow tof fot)-}
    
    {-narrow :: [CRule] -> [CRule] -> Maybe [CRule]-}
    {-[>narrow tof fot | trace ("narrow: " ++ show (map prettyR . fst $ unzip tof, map prettyR . fst $ unzip fot)) False = undefined<]-}
    {-narrow tof fot = sequence $ do-}
      {-f@(r1,c1) <- tof-}
      {-(r2,c2)   <- rename f `liftM` fot-}
      {-let -}
        {-mr = do -}
          {-mu <- mgu (R.rhs r1) (R.lhs r2)-}
          {-let -}
            {-l3 = substitutevars mu (R.lhs r1)-}
            {-r3 = substitutevars mu (R.rhs r2)-}
            {-c3 = mkc (C.mapvars (mkcmap mu) `liftM` c1) (C.mapvars (mkcmap mu) `liftM` c2)-}
          {-return (R.Rule l3 r3, c3)-}
      {-return mr-}
    {-prettyR (R.Rule l r) = hang 2 $ prettyT l <+> text "->" </> prettyT r-}
    {-prettyT (R.Var x)    = text x-}
    {-prettyT (R.Fun f []) = text f-}
    {-prettyT (R.Fun f ts) = text f <> args-}
      {-where args = encloseSep lparen rparen comma [prettyT ti | ti <- ts]-}

    {-[>mgu t1 t2 | trace ("unifu" ++ show (t1,t2)) False = undefined<]-}
    {-mgu t1 t2 = unifyterms [t1] [t2]-}
    {-mkcmap mu v@CVar{} = fromTerm . mu $ toTerm v-}
      {-where -}
        {-toTerm (CVar s) = R.Var s-}
        {-fromTerm (R.Var s)          = CVar s-}
        {-fromTerm (R.Fun "false" []) = BConst False-}
        {-fromTerm (R.Fun "true" [])  = BConst True-}
        {-fromTerm t@(R.Fun s [])       = IConst $ err t `fromMaybe` (readMaybe s :: Maybe Int)-}
        {-fromTerm (R.Fun "$not" [t])     = Not $ fromTerm t-}
        {-fromTerm (R.Fun "$and" [t1,t2]) = fromTerm t1 `And` fromTerm t2-}
        {-fromTerm (R.Fun "$or"  [t1,t2]) = fromTerm t1 `Or`  fromTerm t2-}
        {-fromTerm (R.Fun "$eq"  [t1,t2]) = fromTerm t1 `Eq`  fromTerm t2-}
        {-fromTerm (R.Fun "$neq" [t1,t2]) = fromTerm t1 `Neq` fromTerm t2-}
        {-fromTerm (R.Fun "$gte" [t1,t2]) = fromTerm t1 `Gte` fromTerm t2-}
        {-fromTerm (R.Fun "$add" [t1,t2]) = fromTerm t1 `Add` fromTerm t2-}
        {-fromTerm (R.Fun "$sub" [t1,t2]) = fromTerm t1 `Sub` fromTerm t2-}
        {-err t = error $ "Jat.Utils.Trs.simplifyRHS.fromTerm: illegal substitution" ++ show t-}
    {-mkcmap _ c = c-}


    {-mkc (Just c1) (Just c2) = Just $ c1 `MAnd` c2-}
    {-mkc (Just c1) Nothing   = Just c1-}
    {-mkc Nothing (Just c2)   = Just c2-}
    {-mkc _ _                 = Nothing-}


{-readMaybe :: Read b => String -> Maybe b-}
{-readMaybe s = case reads s of-}
  {-[(x, "")] -> Just x-}
  {-_ -> Nothing-}

 





-- | A pretty printer for a list of constrained term rewrite rule.
prettyTRS :: [(R.Rule PA.PAFun PA.PAVar, [PA.PATerm])] -> Doc
prettyTRS crules =
  header crules
  <$> vsep (map prettyPARule crules)
  <$> footer


{--- | A pretty printer for a list of integer term rewrite rules.-}
{-prettyITRS :: [R.Rule String String] -> Doc-}
{-prettyITRS rules = -}
  {-header rules-}
  {-<$> vsep (map prettyR rules)-}
  {-<$> footer-}
  {-where-}
    {-prettyR (R.Rule l r) = hang 2 $ prettyT l <+> text "->" </> prettyT r-}
    {-prettyT (R.Fun "$not" [t])     = char '!' <+> prettyT t-}
    {-prettyT (R.Fun "$and" [t1,t2]) = prettyT t1 <+> text "&&" <+> prettyT t2-}
    {-prettyT (R.Fun "$or"  [t1,t2]) = prettyT t1 <+> text "||" <+> prettyT t2-}
    {-prettyT (R.Fun "$eq"  [t1,t2]) = prettyT t1 <+> text "=" <+> prettyT t2-}
    {-prettyT (R.Fun "$neq" [t1,t2]) = prettyT t1 <+> text "!=" <+> prettyT t2-}
    {-prettyT (R.Fun "$gte" [t1,t2]) = prettyT t1 <+> text ">=" <+> prettyT t2-}
    {-prettyT (R.Fun "$add" [t1,t2]) = prettyT t1 <+> text "+" <+> prettyT t2-}
    {-prettyT (R.Fun "$sub" [t1,t2]) = prettyT t1 <+> text "-" <+> prettyT t2-}
    {-prettyT (R.Var x)    = text x-}
    {-prettyT (R.Fun f []) = text f-}
    {-prettyT (R.Fun f ts) = text f <> args-}
      {-where args = encloseSep lparen rparen comma [prettyT ti | ti <- ts]-}
      
{--- | Transforms a (restricted) constrained TRS to an integer TRS.-}
{-toITRS :: [(R.Rule String String, Maybe Constraint)] -> [R.Rule String String]-}
{-toITRS = map mapRule-}
  {-where-}
    {-mapRule (R.Rule{R.lhs=l,R.rhs=r},Just c)  = R.Rule (mapTerm l c) (mapTerm r c)-}
    {-mapRule (r,_)                       = r-}
    {-mapTerm t c                         = T.fold (assignment c) R.Fun t-}

    {-assignment (Ass (CVar v1) c) v2 -}
      {-| v1 == v2  =  op c-}
      {-| otherwise =  R.Var v2-}
    {-op (Not c)       = R.Fun "$not" [el c]-}
    {-op (And c d)     = R.Fun "$and" [el c,el d]-}
    {-op (Or  c d)     = R.Fun "$or"  [el c,el d]-}
    {-op (Eq  c d)     = R.Fun "$eq"  [el c,el d]-}
    {-op (Neq c d)     = R.Fun "$neq" [el c,el d]-}
    {-op (Gte c d)     = R.Fun "$gte" [el c,el d]-}
    {-op (Add c d)     = R.Fun "$add" [el c,el d]-}
    {-op (Sub c d)     = R.Fun "$sub" [el c,el d]-}
    {-op e@(BConst _) = el e-}
    {-op _             = error "Jat.Utils.TRS.toITRS: invalid format."-}
    {-el (CVar v)      = R.Var v-}
    {-el (IConst i)    = R.Fun (show i) []-}
    {-el (BConst b)    = R.Fun (show b) []-}
    {-el _             = error "Jat.Utils.TRS.toITRS: invalid format."-}


{-prettyCTRS :: [(R.Rule String String, Maybe Constraint)] -> Doc-}
{-prettyCTRS crules = vcat [logic, signature, rules, kind, query, eof]-}
  {-where-}
    {-logic = text "THEORY ints ;" <$> text "LOGIC QF_LIA ;" <$> text "SOLVER internal ;"-}
    {-signature = text "SIGNATURE" <$> (indent 2 $ prettyfuns (allfuns (fst $ unzip crules))) <$> (indent 2 $ text "!INTEGER ;")-}
      {-where-}
        {-allfuns               = filter theory . nub . concatMap rulefuns-}
        {-theory f              = not $ or [isInt f, isOp f]-}
          {-where-}
            {-isInt s = maybe False (const True) (readMaybe s :: Maybe Int)-}
            {-isOp  s = any (s ==) ["$not", "$and", "$or", "$eq", "$neq", "$gte", "$add", "$sub", "true", "false"]-}
        {-prettyfuns fs         = vsep (map (\f -> text f <+> char ';') fs)-}
        {-rulefuns r            = termfuns(R.lhs r) ++ termfuns (R.rhs r)-}
        {-termfuns (R.Var _)    = []-}
        {-termfuns (R.Fun f ts) = f : concatMap termfuns ts-}
    {-rules = text "RULES"  <$> (indent 2 $ vsep (map prettyR (reverse crules)))-}
      {-where-}
        {-prettyR (R.Rule l r, c)  = prettyT l <+> text "->" </> prettyT r <+> prettyC c <+> char ';'-}
        {-prettyT (R.Fun "$not" [t])     = text "not" <> (parens $ prettyT t)-}
        {-prettyT (R.Fun "$and" [t1,t2]) = prettyT t1 <+> text "/\\" <+> prettyT t2-}
        {-prettyT (R.Fun "$or"  [t1,t2]) = prettyT t1 <+> text "\\/" <+> prettyT t2-}
        {-prettyT (R.Fun "$eq"  [t1,t2]) = prettyT t1 <+> text "=" <+> prettyT t2-}
        {-prettyT (R.Fun "$neq" [t1,t2]) = prettyT t1 <+> text "!=" <+> prettyT t2-}
        {-prettyT (R.Fun "$gte" [t1,t2]) = prettyT t1 <+> text ">=" <+> prettyT t2-}
        {-prettyT (R.Fun "$add" [t1,t2]) = prettyT t1 <+> text "+" <+> prettyT t2-}
        {-prettyT (R.Fun "$sub" [t1,t2]) = prettyT t1 <+> text "-" <+> prettyT t2-}
        {-prettyT (R.Var x)    = text x-}
        {-prettyT (R.Fun f []) = text f-}
        {-prettyT (R.Fun f ts) = text f <> args-}
          {-where args = encloseSep lparen rparen comma [prettyT ti | ti <- ts]-}
        {-prettyC Nothing    = empty-}
        {-prettyC (Just c)   = text "<--" <+> lbracket <> pretty c <> rbracket-}
    {-kind  = text "NON-STANDARD"-}
    {-query = text "QUERY termination"-}
    {-eof   = text "END OF FILE"-}

{--- | ctrl format c. k.-}
  {--- todo : change constraints -- maybe problem with and and so on-}
{-toCTRS :: [(R.Rule String String, Maybe Constraint)] -> [(R.Rule String String, Maybe Constraint)]-}
{-toCTRS = foldRule . map mapRule-}
  {-where-}
    {-mapRule (R.Rule{R.lhs=l,R.rhs=r},Just c)  = (R.Rule (mapTerm l c) (mapTerm r c), isCon c)-}
    {-mapRule (r,c)                       = (r, c) -}
    {-mapTerm t c                         = T.fold (assignment c) R.Fun t-}

    {-isCon c@(Ass (CVar _) (Eq _ _))  = Just c-}
    {-isCon c@(Ass (CVar _) (Neq _ _)) = Just c-}
    {-isCon c@(Ass (CVar _) (Gte _ _)) = Just c-}
    {-isCon c@(Ass (CVar _) (Not _))   = Just c-}
    {-isCon c@(Ass (CVar _) (And _ _)) = Just c-}
    {-isCon c@(Ass (CVar _) (Or _ _))  = Just c-}
    {-isCon _                           = Nothing-}

    {-isCon2 (Eq _ _)  = True-}
    {-isCon2 (Neq _ _) = True-}
    {-isCon2 (Gte _ _) = True-}
    {-isCon2 (Not _)   = True-}
    {-isCon2 (And _ _) = True-}
    {-isCon2 (Or _ _)  = True-}
    {-isCon2 _         = False-}

    {-assignment (Ass (CVar v1) c) v2 -}
      {-| isCon2 c = R.Var v2-}
      {-| v1 == v2  =  op c-}
      {-| otherwise =  R.Var v2-}
    {-[>op (Not c)       = R.Fun "$not" [el c]<]-}
    {-[>op (And c d)     = R.Fun "$and" [el c,el d]<]-}
    {-[>op (Or  c d)     = R.Fun "$or"  [el c,el d]<]-}
    {-op (Add c d)     = R.Fun "$add" [el c,el d]-}
    {-op (Sub c d)     = R.Fun "$sub" [el c,el d]-}
    {-op e@(BConst _) = el e-}
    {-[>op e             = e<]-}
    {-op e             = error $ "Jat.Utils.TRS.toCTRS: invalid format: " ++ show e-}
    {-el (CVar v)      = R.Var v-}
    {-el (IConst i)    = R.Fun (show i) []-}
    {-el (BConst b)    = R.Fun (map C.toLower $ show b) []-}
    {-el _             = error "Jat.Utils.TRS.toCTRS: invalid format."-}


    {-foldRule = foldl k []-}
      {-where -}
        {-k acc (R.Rule{R.lhs=l,R.rhs=r},Just c)  = -}
          {-(R.Rule l (mapTrue r c), Just (toCon c)) : (R.Rule l (mapFalse r c), Just (Not $ toCon c)) : acc-}
        {-k acc (r,c) = (r,c) : acc-}
        {-mapTrue  t c                         = T.fold (toBool c "true") R.Fun t-}
        {-mapFalse t c                         = T.fold (toBool c "false") R.Fun t-}
        {-toBool (Ass (CVar v1) _) s v2 -}
          {-| v1 == v2  =  R.Fun s []-}
          {-| otherwise =  R.Var v2-}
        {-toCon (Ass (CVar _) c) = c-}
        {-toCon _                = error "Jat.Utils.TRS.toCon: invalid format."-}
    {-mgu t1 t2 = unifyterms [t1] [t2]-}
    {-mkcmap mu v@CVar{} = fromTerm . mu $ toTerm v-}
      {-where -}
        {-toTerm (CVar s) = R.Var s-}
        {-fromTerm (R.Var s)          = CVar s-}
        {-fromTerm (R.Fun "false" []) = BConst False-}
        {-fromTerm (R.Fun "true" [])  = BConst True-}
        {-fromTerm t@(R.Fun s [])       = IConst $ err t `fromMaybe` (readMaybe s :: Maybe Int)-}
        {-fromTerm (R.Fun "$not" [t])     = Not $ fromTerm t-}
        {-fromTerm (R.Fun "$and" [t1,t2]) = fromTerm t1 `And` fromTerm t2-}
        {-fromTerm (R.Fun "$or"  [t1,t2]) = fromTerm t1 `Or`  fromTerm t2-}
        {-fromTerm (R.Fun "$eq"  [t1,t2]) = fromTerm t1 `Eq`  fromTerm t2-}
        {-fromTerm (R.Fun "$neq" [t1,t2]) = fromTerm t1 `Neq` fromTerm t2-}
        {-fromTerm (R.Fun "$gte" [t1,t2]) = fromTerm t1 `Gte` fromTerm t2-}
        {-fromTerm (R.Fun "$add" [t1,t2]) = fromTerm t1 `Add` fromTerm t2-}
        {-fromTerm (R.Fun "$sub" [t1,t2]) = fromTerm t1 `Sub` fromTerm t2-}
        {-err t = error $ "Jat.Utils.Trs.simplifyRHS.fromTerm: illegal substitution" ++ show t-}
    {-mkcmap _ c = c-}

