{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- | This module provides functionality for constrained Term rewrite systems (cTRS).
module Jat.Utils.TRS
  (
    prettyTRS
  , simplifyTRS
  , toCTRS
  , prettyCTRS
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

-- old mgu
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


-- | A pretty printer for a list of constrained term rewrite rule.
prettyTRS :: [(R.Rule PA.PAFun PA.PAVar, [PA.PATerm])] -> Doc
prettyTRS crules =
  header crules
  <$> vsep (map prettyPARule crules)
  <$> footer

