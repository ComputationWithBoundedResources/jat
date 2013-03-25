module Jat.PState.Step where

import Jat.Constraints

data Step a b =
    Evaluation (a,Constraint)
  | Refinement [(b,Constraint)]
  | Abstraction (a,Constraint)
  deriving Show

type PStep a = Step a a

evaluation :: a -> Constraint -> Step a b
evaluation = curry Evaluation

topEvaluation :: a -> Step a b
topEvaluation a = evaluation a top

map2 :: (a -> c) -> (b -> d) -> Step a b -> Step c d
map2 f _ (Evaluation (a,c))  = Evaluation (f a,c)
map2 _ g (Refinement bs)     = Refinement [(g b,c) | (b,c) <- bs]
map2 f _ (Abstraction (a,c)) = Abstraction (f a,c)

liftStep :: (a -> c) -> (b -> d) -> Step a b -> Step c d
liftStep = map2

liftPStep :: (a -> b) -> PStep a -> PStep b
liftPStep f = map2 f f

