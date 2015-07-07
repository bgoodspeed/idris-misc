module SetEq

-- TODONOTE declaring exports is not done at module ASDF Method, Method2 etc, it is done by a visibility declaration.


--import Data.List (delete)

{-- Sets implemented as unordered lists without duplicates --} 

-- TODONOTE no newtype equivalent decorator, we 
data MySet a = MySetCons (List a)


inMySet  : (Eq a) => a -> MySet a -> Bool  
inMySet x (MySetCons s) = elem x s


-- TODONOTE this definition fails the totality checker, because it can't tell that the recursive call is on a smaller argument
%assert_total
subMySet : (Eq a) => MySet a -> MySet a -> Bool
subMySet (MySetCons [])     _   = True  
subMySet (MySetCons (x::xs)) set = (inMySet x set) && subMySet (MySetCons xs) set 


instance (Eq a) => Eq (MySet a) where 
  set1 == set2 = subMySet set1 set2 && subMySet set2 set1

-- TODONOTE not sure what this is trying to do, must revisit this
showMySet : (Show a) =>  MySet a -> String
showMySet (MySetCons list) = show list 

-- TODONOTE instance declarations may only define the methods in the typeclass (no more nor less)

instance (Show a) => Show (MySet a) where
  show = showMySet


emptyMySet  : MySet a       
emptyMySet = MySetCons []

isEmpty  : MySet a -> Bool            
isEmpty (MySetCons []) = True
isEmpty  _       = False 

insertMySet : (Eq a) => a -> MySet a -> MySet a 
insertMySet x (MySetCons ys) = if inMySet x (MySetCons ys) then MySetCons ys else MySetCons (x :: ys)

deleteMySet : Eq a => a -> MySet a -> MySet a 
deleteMySet x (MySetCons xs) = MySetCons (delete x xs)

list2set : Eq a => List a -> MySet a
list2set [] = MySetCons []
list2set (x::xs) = insertMySet x (list2set xs)

-- TODONOTE idris is not fond of [[a]], need List (List a)
powerList  : List a -> List (List a) 
powerList  [] = [[]]
powerList  (x::xs) = (powerList xs) ++ (map (x::) (powerList xs))

--TODONOTE syntax different for lambdas \ x -> body becomes  \x => body
powerMySet : Eq a => MySet a -> MySet (MySet a)
powerMySet (MySetCons xs) = MySetCons (map (\xs => (MySetCons xs)) (powerList xs))


-- TODONOTE take requires a Nat (for pattern matching), can either change sig from int to nat for takeMySet or call (cast theInt) to get the required nat argument
takeMySet : Eq a => Nat -> MySet a -> MySet a
takeMySet n (MySetCons xs) = MySetCons (take n xs) 


-- TODONOTE index requires a proof that n is shorter, otherwise we must use index' which returns a Maybe type.
infixl 9 !!!
(!!!) : Eq a => MySet a -> Nat -> Maybe a
(MySetCons xs) !!! n = index' n xs 


