module Jat.CompGraph where


-- finding instance/merge nodes for backjumps
-- assumptions: 
-- * code is unstructured, i.e. decomposition in general not possible (besides method calls)
-- * if there are multiple candidates then one is the predecessor of the other one
--   i.e. c1 ->n -> c2 ->n e is valid but c1 ->n e, c2 ->n e, c1 /->n c2, c2 /-> c1 not
--   then predecessor is defined by wrt. to the transivity relation

-- 1. decompose in method calls
-- 2. find candidates
-- 3. sort candidates wrt. to transivity relation


