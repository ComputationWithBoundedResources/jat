-- | This module provides functionality for constrained Term rewrite systems (cTRS).
module Jat.Utils.TRS
  (
    prettyTRS
  , prettyITRS
  , toITRS
  )

where

import Jat.Utils.Pretty
import Jat.Constraints
import Data.Rewriting.Rule 
import Data.Rewriting.Term (fold) 
import Data.List (nub)

import Debug.Trace

header :: [Rule String String] -> Doc
header rules = 
  lparen <> text "VAR" <+> prettyvars (allvars rules) <> rparen
  <$> lparen <> text "RULES" 
  where
    allvars   = nub .  concatMap rulevars
    prettyvars vs = hsep (map text vs)
    rulevars r          = termvars (lhs r) ++ termvars (rhs r)
    termvars (Var v)    = [v]
    termvars (Fun _ ts) = concatMap termvars ts

footer :: Doc
footer = rparen

-- | A pretty printer for a list of constrained term rewrite rule.
prettyTRS :: [(Rule String String, Maybe Constraint)] -> Doc
prettyTRS crules = 
  header rules
  <$> vsep (map2 (prettyRule (text "->") pretty pretty) prettyCon `fmap` crules)
  <$> footer 
  where
    (rules,_) = unzip crules
    map2 f g (a,b) = f a <+> g b
    prettyCon Nothing    = empty
    prettyCon (Just con) = char '|' <+> pretty con


-- | A pretty printer for a list of integer term rewrite rules.
prettyITRS :: [Rule String String] -> Doc
prettyITRS rules = 
  header rules
  <$> vsep (map prettyR rules)
  <$> footer
  where
    prettyR (Rule l r) = hang 2 $ prettyT l <+> text "->" </> prettyT r
    prettyT (Fun "$not" [t])     = char '!' <+> prettyT t
    prettyT (Fun "$and" [t1,t2]) = prettyT t1 <+> text "&&" <+> prettyT t2
    prettyT (Fun "$or"  [t1,t2]) = prettyT t1 <+> text "||" <+> prettyT t2
    prettyT (Fun "$eq"  [t1,t2]) = prettyT t1 <+> text "=" <+> prettyT t2
    prettyT (Fun "$neq" [t1,t2]) = prettyT t1 <+> text "!=" <+> prettyT t2
    prettyT (Fun "$gte" [t1,t2]) = prettyT t1 <+> text ">=" <+> prettyT t2
    prettyT (Fun "$add" [t1,t2]) = prettyT t1 <+> text "+" <+> prettyT t2
    prettyT (Fun "$sub" [t1,t2]) = prettyT t1 <+> text "-" <+> prettyT t2
    prettyT (Var x)    = text x
    prettyT (Fun f []) = text f
    prettyT (Fun f ts) = text f <> args
      where args = encloseSep lparen rparen comma [prettyT ti | ti <- ts]
      
toITRS :: [(Rule String String, Maybe Constraint)] -> [Rule String String]
{-toITRS rules = let r = map mapRule rules in trace (show . prettyTRS $ zip r (cycle [Nothing])) r-}
toITRS = map mapRule
  where
    mapRule (Rule{lhs=l,rhs=r},Just c)  = Rule (mapTerm l c) (mapTerm r c)
    mapRule (r,_)                       = r
    mapTerm t c                         = fold (assignment c) Fun t

    {-assignment c v | trace (show (c,v)) False = undefined-}
    assignment (Ass (CVar v1) c) v2 
      | v1 == v2  = trace (show (v1,v2,v1==v2)) $ op c
      | otherwise = trace "NOP" $ Var v2
    op (Not c)    = Fun "$not" [el c]
    op (And c d)  = Fun "$and" [el c,el d]
    op (Or  c d)  = Fun "$or"  [el c,el d]
    op (Eq  c d)  = Fun "$eq"  [el c,el d]
    op (Neq c d)  = Fun "$neq" [el c,el d]
    op (Gte c d)  = Fun "$gte" [el c,el d]
    op (Add c d)  = Fun "$add" [el c,el d]
    op (Sub c d)  = Fun "$sub" [el c,el d]
    el (CVar v)   = Var v
    el (IConst i) = Fun (show i) []
    el (BConst b) = Fun (show b) []


