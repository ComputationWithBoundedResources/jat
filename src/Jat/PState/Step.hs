-- | This module provides a program step.  A step can be an evaluation, a
-- refinement or an abstraction.
module Jat.PState.Step 
  (
    Step (..)
  , PStep
  , evaluation
  , topEvaluation
  , topRefinement
  , liftStep
  , liftPStep
  )
where

import Jat.Constraints

-- | The type of a step.
data Step a b =
    Evaluation (a,Constraint)
  | Refinement [(b,Constraint)]
  | Abstraction (a,Constraint)
  deriving Show

-- | The type of a program step.
type PStep a = Step a a

-- | Performs an evaluation step.
evaluation :: a -> Constraint -> Step a b
evaluation = curry Evaluation

-- | Performs an evaluation step constrained with top.
topEvaluation :: a -> Step a b
topEvaluation a = evaluation a top

-- | Performs an refinement step  constrained with top .
topRefinement :: [b] -> Step a b
topRefinement bs = Refinement $ zip bs (cycle [top])

map2 :: (a -> c) -> (b -> d) -> Step a b -> Step c d
map2 f _ (Evaluation (a,c))  = Evaluation (f a,c)
map2 _ g (Refinement bs)     = Refinement [(g b,c) | (b,c) <- bs]
map2 f _ (Abstraction (a,c)) = Abstraction (f a,c)

-- | Lifts two function to a step.
liftStep :: (a -> c) -> (b -> d) -> Step a b -> Step c d
liftStep = map2

-- | Lifts a function to a program step.
liftPStep :: (a -> b) -> PStep a -> PStep b
liftPStep f = map2 f f

