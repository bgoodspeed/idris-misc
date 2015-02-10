module Utilities



filterStream : (a -> Bool) -> Stream a -> Stream a
filterStream p (x :: y) = if p x 
                             then x :: filterStream p y
                             else filterStream p y
                                 

-- TODONOTE init is only available on cons versions, need to use init' or provide the proof (it should be the case that divs has always got at least one element)
-- TODONOTE this is the unsafe version
unsafeInit : (l : List a) -> List a
unsafeInit [x]        = []
unsafeInit (x::y::ys) = x :: unsafeInit (y::ys) 


cyclicShift : List a -> List a
cyclicShift [] = []  
cyclicShift (x :: xs) = xs ++ [x] 

iterateN : Nat -> (f : a -> a) -> (x : a) -> List a
iterateN Z     f x = []  
iterateN (S n) f x = x :: iterateN n f (f x)

permutations : (Eq a) => List a -> List (List a)
permutations [] = [[]] 
permutations xs = [x::ys | x <- xs, ys <- permutations (delete x xs)] 

mapM_ : Monad m => (a -> m b) -> List a -> m() 
mapM_ f  = sequence_ . map f

