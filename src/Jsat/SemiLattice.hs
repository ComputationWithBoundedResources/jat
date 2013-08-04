{-# LANGUAGE TypeFamilies #-}
module Jsat.SemiLattice where

import Jsat.Q

-- (abstract) value
class SemiLattice l where
  data Val :: *
  name :: l -> String
  bot  :: l -> Val 
  join :: l -> Q -> Val -> Val -> Val 



