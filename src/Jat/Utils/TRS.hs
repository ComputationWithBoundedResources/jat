module Jat.Utils.TRS
  (prettyTRS)
where

import Jat.Utils.Pretty
import Jat.Constraints (Constraint)
import Data.Rewriting.Rule 
import Data.List (nub)


prettyTRS :: [(Rule String String, Maybe Constraint)] -> Doc
prettyTRS crules = 
  lparen <+> text "VARS" <+> prettyvars (allvars rules) <+> rparen
  <$> lparen <+> text "RULES" 
  <$> vsep (map2 (prettyRule (text "->") pretty pretty) prettyCon `fmap` crules)
  <$> rparen
  where
    allvars   = nub .  concatMap rulevars
    (rules,_) = unzip crules
  
    map2 f g (a,b) = f a <+> g b
    prettyvars vs = hsep (map text vs)
    rulevars r          = termvars (lhs r) ++ termvars (rhs r)
    termvars (Var v)    = [v]
    termvars (Fun _ ts) = concatMap termvars ts
    prettyCon Nothing    = empty
    prettyCon (Just con) = char '|' <+> pretty con

