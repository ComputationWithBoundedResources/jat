module Jat.Utils.TRS
  (prettyTRS)
where

import Jat.Utils.Pretty
import Data.Rewriting.Rule 
import Data.List (nub)



prettyTRS :: [Rule String String] -> Doc
prettyTRS rules = 
  lparen <+> text "VARS" <+> prettyvars (allvars rules) <+> rparen
  <$> lparen <+> text "RULES" 
  <$> vsep (map (prettyRule (text "->") pretty pretty) rules)
  <$> rparen
  where
    allvars = nub .  concatMap rulevars
  
    prettyvars vs = hsep (map text vs)
    rulevars r = termvars (lhs r) ++ termvars (rhs r)
    termvars (Var v) = [v] 
    termvars (Fun _ ts) = concatMap termvars ts

