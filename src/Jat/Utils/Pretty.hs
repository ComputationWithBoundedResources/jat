{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

-- | This module export the ANSI.Leijen pretty printer library.
module Jat.Utils.Pretty 
  (
    Pretty
  , pretty
  , display
  , module Text.PrettyPrint.ANSI.Leijen
  )
where

import Text.PrettyPrint.ANSI.Leijen hiding (Pretty,pretty)

-- | The 'Pretty' class.
class Pretty a where
  pretty :: a -> Doc

instance Pretty String where
  pretty = text

-- | Renders a Doc suitably.
display :: Doc -> String
display d = displayS (renderPretty 0.9 1000 d)  ""


