-- | This module exports the 'Program' type and related functions.
module Jat.Program
  (
    module Jat.Program.Data 
  , module Jat.Program.Fun
  )
where

import Jat.Program.Data hiding (ClassPool, FieldPool, MethodPool, initP)
import Jat.Program.Fun

