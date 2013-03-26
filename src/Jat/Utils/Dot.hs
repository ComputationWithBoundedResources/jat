module Jat.Utils.Dot where

import Data.Text.Lazy 
import Data.GraphViz.Types.Canonical (DotGraph)
import Data.GraphViz.Printing (renderDot,toDot)


dot2String :: DotGraph Int -> String
dot2String = unpack . leftAlign . renderDot . toDot
  where
    leftAlign = replace (pack "\\n") (pack "\\l")

