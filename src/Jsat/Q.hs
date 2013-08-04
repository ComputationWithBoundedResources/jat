module Jsat.Q where

import Jsat.Program

data Q = Q Program

qprogram :: Q -> Program
qprogram (Q p) = p
