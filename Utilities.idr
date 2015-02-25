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

iterateN : Nat -> (f : a -> a) -> (x : a) -> List a
iterateN Z     f x = []  
iterateN (S n) f x = x :: iterateN n f (f x)


applyN : Nat -> (f : a -> a) -> a -> a
applyN Z f x = x 
applyN (S k) f x = applyN k f (f x)



cyclicShift : List a -> List a
cyclicShift [] = []  
cyclicShift (x :: xs) = xs ++ [x] 

allCyclicShiftsOf : List a -> List (List a)
allCyclicShiftsOf xs = iterateN (length xs) cyclicShift xs



permutations : (Eq a) => List a -> List (List a)
permutations [] = [[]] 
permutations xs = [x::ys | x <- xs, ys <- permutations (delete x xs)] 

mapM_ : Monad m => (a -> m b) -> List a -> m() 
mapM_ f  = sequence_ . map f

unsafeZip : List a -> List b -> List (a, b)
unsafeZip [] bs = []
unsafeZip as [] = []
unsafeZip (a::as) (b::bs) = (a,b) :: unsafeZip as bs

prefixesOf : String -> List String
prefixesOf w with (unpack w)
    | [] = []
    | xs = let segs = inits xs in
               map pack segs

powerList  : List a -> List (List a)
powerList  [] = [[]]
powerList  (x::xs) = (powerList xs) ++ (map (x::) (powerList xs))

orderedSubsets : (Eq a) => List a -> List (List a)
orderedSubsets [] = [] 
orderedSubsets (x :: xs) = (inits (x :: xs)) ++ (orderedSubsets xs)

-- Similar to nub

uniqueElements : (Eq a) => List a -> List a
uniqueElements [] = []
uniqueElements (x :: xs) = if x `elem` xs then uniqueElements xs else x :: uniqueElements xs 



-- TODONOTE ported liftm2 from haskell (equivalent to liftA2)

liftM2 : (Monad m) => (a1 -> a2 -> r) -> m a1 -> m a2 -> m r
liftM2 f m1 m2 = do { x1 <- m1 ; x2 <- m2; return (f x1 x2) }
               
