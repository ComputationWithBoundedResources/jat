{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module Jat.Utils.Pretty 
  (
    Pretty
  , pretty
  , display
  , module Text.PrettyPrint.ANSI.Leijen
  )
where

import Text.PrettyPrint.ANSI.Leijen hiding (Pretty,pretty)

class Pretty a where
  pretty :: a -> Doc

instance Pretty String where
  pretty = text

display :: Doc -> String
display d = displayS (renderPretty 0.9 1000 d)  ""


