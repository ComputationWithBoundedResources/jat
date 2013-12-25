-- | This module exports the 'Program' type and related functionalities..
module Jinja.Program
  (
    module Jinja.Program.Data 
  , module Jinja.Program.Fun
  )
where

import Jinja.Program.Data hiding (ClassPool, FieldPool, MethodPool, initP)
import Jinja.Program.Fun

