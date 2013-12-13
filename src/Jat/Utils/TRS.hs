-- | This module provides functionality for constrained Term rewrite systems (cTRS).
module Jat.Utils.TRS
  (
    prettyTRS
  , prettyITRS
  , prettyCTRS
  , toITRS
  , toCTRS
  
  , simplifyRHS
  )

where

import Jat.Utils.Pretty
import Jat.Constraints as C
import qualified Data.Rewriting.Rule as R
import qualified Data.Rewriting.Term as T
import Data.List as L
import Data.Char as C
import Data.Maybe (fromMaybe, catMaybes)
import Control.Monad (liftM)

import Debug.Trace

-- TODO: Constraint type should generalize Term from rewriting lib

-- NOTE:
-- aprove and irs: works differently when using constraint syntax

header :: [R.Rule String String] -> Doc
header rules = 
  lparen <> text "VAR" <+> prettyvars (allvars rules) <> rparen
  <$> lparen <> text "RULES" 
  where
    allvars   = nub .  concatMap rulevars
    prettyvars vs = hsep (map text vs)
    rulevars r          = termvars (R.lhs r) ++ termvars (R.rhs r)
    termvars (R.Var v)    = [v]
    termvars (R.Fun _ ts) = concatMap termvars ts

footer :: Doc
footer = rparen

type CRule = (R.Rule String String, Maybe Constraint)

-- simplify according to (refused) RTA2013 paper
-- we additionally require that |Rf->| = 1; and constraint is Nothing
simplifyRHS :: [CRule] -> [CRule]
simplifyRHS crules = foldl clean crules (funs crules)
  where
    clean rules f
      | null (tof `intersect` fot)
        {-&& length fot == 1-}
        && not (null tof)
        && not (null fot)
        {-&& all nothing fot-}
        && all linear tof
        = cleanF tof fot rules
      {-| null (tof `intersect` fot) && length fot == 1 = cleanF tof fot rules-}
      | otherwise = rules
      where
        tof = toF f rules
        fot = foT f rules
        nothing (_,Nothing) = True
        nothing _           = False
        linear (r,_)        = all (`elem` T.vars (R.lhs r)) (T.vars (R.rhs r))

    funs rules = nub $ map (\(r,_) -> root (R.lhs r)) rules
    toF f = filter k where k (r,_) = root (R.rhs r) == f
    foT f = filter k where k (r,_) = root (R.lhs r) == f
    cleanF tof fot rules = 
      rules `fromMaybe` ((((rules \\ tof) \\ fot) ++) `liftM` narrow tof fot)
    
    narrow :: [CRule] -> [CRule] -> Maybe [CRule]
    narrow tof fot | trace ("narrow: " ++ show (map prettyR . fst $ unzip tof, map prettyR . fst $ unzip fot)) False = undefined
    narrow tof fot = sequence $ do
      f@(r1,c1) <- tof
      (r2,c2)   <- rename f `liftM` fot
      let 
        mr = do 
          mu <- mgu (R.rhs r1) (R.lhs r2)
          let 
            l3 = substitutevars mu (R.lhs r1)
            r3 = substitutevars mu (R.rhs r2)
            c3 = C.mapvars (mkcmap mu) `liftM` mkc c1 c2
          return (R.Rule l3 r3, c3)
      return mr
    prettyR (R.Rule l r) = hang 2 $ prettyT l <+> text "->" </> prettyT r
    prettyT (R.Var x)    = text x
    prettyT (R.Fun f []) = text f
    prettyT (R.Fun f ts) = text f <> args
      where args = encloseSep lparen rparen comma [prettyT ti | ti <- ts]

    {-mgu t1 t2 | trace ("unifu" ++ show (t1,t2)) False = undefined-}
    mgu t1 t2 = unifyterms [t1] [t2]
    mkcmap mu v@CVar{} = fromTerm . mu $ toTerm v
      where 
        toTerm (CVar s) = R.Var s
        fromTerm (R.Var s)          = CVar s
        fromTerm (R.Fun "flase" []) = BConst False
        fromTerm (R.Fun "true" [])  = BConst True
        fromTerm t@(R.Fun s [])       = IConst $ err t `fromMaybe` (readMaybe s :: Maybe Int)
        fromTerm (R.Fun "$not" [t])     = Not $ fromTerm t
        fromTerm (R.Fun "$and" [t1,t2]) = fromTerm t1 `And` fromTerm t2
        fromTerm (R.Fun "$or"  [t1,t2]) = fromTerm t1 `Or`  fromTerm t2
        fromTerm (R.Fun "$eq"  [t1,t2]) = fromTerm t1 `Eq`  fromTerm t2
        fromTerm (R.Fun "$neq" [t1,t2]) = fromTerm t1 `Neq` fromTerm t2
        fromTerm (R.Fun "$gte" [t1,t2]) = fromTerm t1 `Gte` fromTerm t2
        fromTerm (R.Fun "$add" [t1,t2]) = fromTerm t1 `Add` fromTerm t2
        fromTerm (R.Fun "$sub" [t1,t2]) = fromTerm t1 `Sub` fromTerm t2
        err t = error $ "Jat.Utils.Trs.simplifyRHS.fromTerm: illegal substitution" ++ show t
    mkcmap _ c = c


    mkc (Just c1) (Just c2) = Just $ c1 `And` c2
    mkc (Just c1) Nothing   = Just c1
    mkc Nothing (Just c2)   = Just c2
    mkc _ _                 = Nothing

    root (R.Var _)   = error "simplify.root: unexpected variable"
    root (R.Fun f _) = f

readMaybe :: Read b => String -> Maybe b
readMaybe s = case reads s of
  [(x, "")] -> Just x
  _ -> Nothing

rename :: CRule -> CRule -> CRule
rename s@(r1,c1) t@(r2,c2)
  | null common = t
  | otherwise = rename s (rename' t)
  where
    cvars c          = [] `fromMaybe` liftM C.vars c
    vars1            = R.vars r1 ++ cvars c1
    vars2            = R.vars r2 ++ cvars c2
    common           = vars1 `intersect` vars2
    rename' (r,c)    = (rmap id varft r, mapvars varfc `liftM` c)
    varft x          = if x `elem` common || x `elem` vars2 then varft $ 'q':x else x
    varfc (C.CVar x) = C.CVar $ varft x
    rmap f g r       = R.Rule (T.map f g (R.lhs r)) (T.map f g (R.rhs r))

{-rename :: R.Term String String -> R.Term String String -> R.Term String String-}
{-rename r l -}
  {-| null common = l-}
  {-| otherwise   = rename r (T.map id varf l)-}
  {-where-}
    {-common = T.vars r `intersect` T.vars l-}
    {-varf x = if x `elem` common then x++"\'" else x-}
  
    
unifyterms :: [R.Term String String] -> [R.Term String String] -> Maybe Substitution
unifyterms = unifyts (Just emptysubstitution)
  where 
    unifyt (R.Var x) (R.Var y) | x == y = Just id
    unifyt (R.Var v1) f      | v1 `elem` T.vars f = Nothing
    unifyt v1@(R.Var _) f = Just (\t -> if t == v1 then f else t)

    unifyt f (R.Var y) = unifyt (R.Var y) f

    unifyt (R.Fun f1 ts1) (R.Fun f2 ts2) 
      | f1 == f2 = unifyts (Just emptysubstitution) ts1 ts2
      | otherwise = Nothing
        
    unifyts s0M [] [] = s0M
    unifyts s0M (t1:ts1) (t2:ts2) = do
      let subst = substitutevars
      s0 <- s0M 
      s1 <- unifyt (subst s0 t1) (subst s0 t2)
      let s2 = return $ compose s0 s1
      unifyts s2 ts1 ts2
    unifyts _ ts1 ts2 = error $ "unifyterms: unexpected case: " ++ show (ts1,ts2)


maptvars :: (R.Term a b-> R.Term a b) -> R.Term a b -> R.Term a b
maptvars f (R.Fun a ts)  = R.Fun a (map (maptvars f) ts)
maptvars f v           = f v

type Substitution = R.Term String String -> R.Term String String

substitutevars :: Substitution -> R.Term String String -> R.Term String String
substitutevars = maptvars

emptysubstitution :: Substitution
emptysubstitution = id

compose :: Substitution -> Substitution -> Substitution
compose sigma tau = tau . sigma



-- | A pretty printer for a list of constrained term rewrite rule.
prettyTRS :: [(R.Rule String String, Maybe Constraint)] -> Doc
prettyTRS crules = 
  header rules
  <$> vsep (map2 prettyR prettyCon `fmap` crules)
  <$> footer 
  where
    (rules,_) = unzip crules
    map2 f g (a,b) = f a <+> g b
    prettyR (R.Rule l r) = hang 2 $ prettyT l <+> text "->" </> prettyT r
    prettyT (R.Var x)    = text x
    prettyT (R.Fun f []) = text f
    prettyT (R.Fun f ts) = text f <> args
      where args = encloseSep lparen rparen comma [prettyT ti | ti <- ts]
    prettyCon Nothing    = empty
    prettyCon (Just con) = char '|' <+> pretty con


-- | A pretty printer for a list of integer term rewrite rules.
prettyITRS :: [R.Rule String String] -> Doc
prettyITRS rules = 
  header rules
  <$> vsep (map prettyR rules)
  <$> footer
  where
    prettyR (R.Rule l r) = hang 2 $ prettyT l <+> text "->" </> prettyT r
    prettyT (R.Fun "$not" [t])     = char '!' <+> prettyT t
    prettyT (R.Fun "$and" [t1,t2]) = prettyT t1 <+> text "&&" <+> prettyT t2
    prettyT (R.Fun "$or"  [t1,t2]) = prettyT t1 <+> text "||" <+> prettyT t2
    prettyT (R.Fun "$eq"  [t1,t2]) = prettyT t1 <+> text "=" <+> prettyT t2
    prettyT (R.Fun "$neq" [t1,t2]) = prettyT t1 <+> text "!=" <+> prettyT t2
    prettyT (R.Fun "$gte" [t1,t2]) = prettyT t1 <+> text ">=" <+> prettyT t2
    prettyT (R.Fun "$add" [t1,t2]) = prettyT t1 <+> text "+" <+> prettyT t2
    prettyT (R.Fun "$sub" [t1,t2]) = prettyT t1 <+> text "-" <+> prettyT t2
    prettyT (R.Var x)    = text x
    prettyT (R.Fun f []) = text f
    prettyT (R.Fun f ts) = text f <> args
      where args = encloseSep lparen rparen comma [prettyT ti | ti <- ts]
      
-- | Transforms a (restricted) constrained TRS to an integer TRS.
toITRS :: [(R.Rule String String, Maybe Constraint)] -> [R.Rule String String]
toITRS = map mapRule
  where
    mapRule (R.Rule{R.lhs=l,R.rhs=r},Just c)  = R.Rule (mapTerm l c) (mapTerm r c)
    mapRule (r,_)                       = r
    mapTerm t c                         = T.fold (assignment c) R.Fun t

    assignment (Ass (CVar v1) c) v2 
      | v1 == v2  =  op c
      | otherwise =  R.Var v2
    op (Not c)       = R.Fun "$not" [el c]
    op (And c d)     = R.Fun "$and" [el c,el d]
    op (Or  c d)     = R.Fun "$or"  [el c,el d]
    op (Eq  c d)     = R.Fun "$eq"  [el c,el d]
    op (Neq c d)     = R.Fun "$neq" [el c,el d]
    op (Gte c d)     = R.Fun "$gte" [el c,el d]
    op (Add c d)     = R.Fun "$add" [el c,el d]
    op (Sub c d)     = R.Fun "$sub" [el c,el d]
    op e@(BConst _) = el e
    op _             = error "Jat.Utils.TRS.toITRS: invalid format."
    el (CVar v)      = R.Var v
    el (IConst i)    = R.Fun (show i) []
    el (BConst b)    = R.Fun (show b) []
    el _             = error "Jat.Utils.TRS.toITRS: invalid format."


prettyCTRS :: [(R.Rule String String, Maybe Constraint)] -> Doc
prettyCTRS crules = vcat [logic, signature, rules, kind, query, eof]
  where
    logic = text "THEORY ints ;" <$> text "LOGIC QF_LIA ;" <$> text "SOLVER internal ;"
    signature = text "SIGNATURE" <$> (indent 2 $ prettyfuns (allfuns (fst $ unzip crules))) <$> (indent 2 $ text "!INTEGER ;")
      where
        allfuns               = filter theory . nub . concatMap rulefuns
        theory f              = not $ or [isInt f, isOp f]
          where
            isInt s = maybe False (const True) (readMaybe s :: Maybe Int)
            isOp  s = any (s ==) ["$not", "$and", "$or", "$eq", "$neq", "$gte", "$add", "$sub", "true", "false"]
        prettyfuns fs         = vsep (map (\f -> text f <+> char ';') fs)
        rulefuns r            = termfuns(R.lhs r) ++ termfuns (R.rhs r)
        termfuns (R.Var _)    = []
        termfuns (R.Fun f ts) = f : concatMap termfuns ts
    rules = text "RULES"  <$> (indent 2 $ vsep (map prettyR (reverse crules)))
      where
        prettyR (R.Rule l r, c)  = prettyT l <+> text "->" </> prettyT r <+> prettyC c <+> char ';'
        prettyT (R.Fun "$not" [t])     = text "not" <> (parens $ prettyT t)
        prettyT (R.Fun "$and" [t1,t2]) = prettyT t1 <+> text "/\\" <+> prettyT t2
        prettyT (R.Fun "$or"  [t1,t2]) = prettyT t1 <+> text "\\/" <+> prettyT t2
        prettyT (R.Fun "$eq"  [t1,t2]) = prettyT t1 <+> text "=" <+> prettyT t2
        prettyT (R.Fun "$neq" [t1,t2]) = prettyT t1 <+> text "!=" <+> prettyT t2
        prettyT (R.Fun "$gte" [t1,t2]) = prettyT t1 <+> text ">=" <+> prettyT t2
        prettyT (R.Fun "$add" [t1,t2]) = prettyT t1 <+> text "+" <+> prettyT t2
        prettyT (R.Fun "$sub" [t1,t2]) = prettyT t1 <+> text "-" <+> prettyT t2
        prettyT (R.Var x)    = text x
        prettyT (R.Fun f []) = text f
        prettyT (R.Fun f ts) = text f <> args
          where args = encloseSep lparen rparen comma [prettyT ti | ti <- ts]
        prettyC Nothing    = empty
        prettyC (Just c)   = text "<--" <+> lbracket <> pretty c <> rbracket
    kind  = text "NON-STANDARD"
    query = text "QUERY termination"
    eof   = text "END OF FILE"

-- | ctrl format c. k.
  -- todo : change constraints -- maybe problem with and and so on
toCTRS :: [(R.Rule String String, Maybe Constraint)] -> [(R.Rule String String, Maybe Constraint)]
toCTRS = simplifyRHS . simplifyRHS . foldRule . map mapRule
  where
    mapRule (R.Rule{R.lhs=l,R.rhs=r},Just c)  = (R.Rule (mapTerm l c) (mapTerm r c), isCon c)
    mapRule (r,c)                       = (r, c) 
    mapTerm t c                         = T.fold (assignment c) R.Fun t

    isCon c@(Ass (CVar _) (Eq _ _))   = Just c
    isCon c@(Ass (CVar _) (Neq _ _))  = Just c 
    isCon c@(Ass (CVar _) (Gte _ _))  = Just c
    isCon _                           = Nothing

    isCon2 (Eq _ _)  = True
    isCon2 (Neq _ _) = True
    isCon2 (Gte _ _) = True
    isCon2 _         = False


    assignment (Ass (CVar v1) c) v2 
      | isCon2 c = R.Var v2
      | v1 == v2  =  op c
      | otherwise =  R.Var v2
    op (Not c)       = R.Fun "$not" [el c]
    op (And c d)     = R.Fun "$and" [el c,el d]
    op (Or  c d)     = R.Fun "$or"  [el c,el d]
    op (Add c d)     = R.Fun "$add" [el c,el d]
    op (Sub c d)     = R.Fun "$sub" [el c,el d]
    op e@(BConst _) = el e
    {-op e             = e-}
    op e             = error $ "Jat.Utils.TRS.toCTRS: invalid format: " ++ show e
    el (CVar v)      = R.Var v
    el (IConst i)    = R.Fun (show i) []
    el (BConst b)    = R.Fun (map C.toLower $ show b) []
    el _             = error "Jat.Utils.TRS.toCTRS: invalid format."


    foldRule = foldl k []
      where 
        k acc (R.Rule{R.lhs=l,R.rhs=r},Just c)  = 
          (R.Rule l (mapTrue r c), Just (toCon c)) : (R.Rule l (mapFalse r c), Just (Not $ toCon c)) : acc
        k acc (r,c) = (r,c) : acc
        mapTrue  t c                         = T.fold (toBool c "true") R.Fun t
        mapFalse t c                         = T.fold (toBool c "false") R.Fun t
        toBool (Ass (CVar v1) _) s v2 
          | v1 == v2  =  R.Fun s []
          | otherwise =  R.Var v2
        toCon (Ass (CVar _) c) = c
        toCon _                = error "Jat.Utils.TRS.toCon: invalid format."

