module Jat.Utils.Stack 
 (
 Stack,
 push,
 pop,
 top,
 split
 )

where

type Stack a = [a]

push :: a -> Stack a -> Stack a
push = (:)

pop :: Stack a -> Stack a
pop []     = error "Jat.Utils.Stack.pop: empty stack"
pop (_:xs) = xs

top :: Stack a -> a
top []    = error "Jat.Utils.Stack.pop: empty stack"
top (x:_) = x

split :: Int -> Stack a -> (Stack a, Stack a) 
split = splitAt
