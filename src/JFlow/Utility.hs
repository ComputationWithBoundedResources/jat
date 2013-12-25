module JFlow.Utility where



-- pipe operator
infixl 1 |>
(|>) :: b -> (b -> c) -> c
(|>) = flip ($) 


-- finite version of zip with
safeZipWith :: (a -> b -> c) -> [a] -> [b] -> [c]
safeZipWith f (a:as) (b:bs) = f a b : zipWith f as bs
safeZipWith _ []     []     = []
safeZipWith _ _      _      = error "lists of different lengths"

