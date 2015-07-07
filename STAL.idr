module STAL 


-- TODONOTE need to figure out how to deal with infinite streams in idris
import DB

small_squares1 : List Nat
small_squares1 = [ n*n | n <- [0..999] ]


small_squares_filtered : List Nat
small_squares_filtered = [ n*n | n <- [0..999], ((mod n 2) == 0) ]

small_squares_filtered_fake : List Nat
small_squares_filtered_fake = [ n*n | n <- [0..999], True ] 


naturals : Stream Nat
naturals = [0..]


evens2 : Stream Nat
evens2 = [ 2*n | n <- naturals ]

-- TODONOTE these ones can't be expressed because the syntax sugar for
-- TODONOTE  [ 2*n | n <- naturals, True ] becomes
-- TODONOTE do n <- naturals; guard True; pure (2*n)
-- TODONOTE where guard : Alternative f => Bool -> f ()
-- TODONOTE stream is not an alternative instance, so it doesn't work
-- TODONOTE stream filtering can't be total "since the stream may hold finitely many elements for which the predicate holds"
-- TODONOTE :t \naturals : Stream Nat => [ 2 * n | n <- naturals ]
-- TODONOTE \naturals => naturals >>= (\n3 => return (fromInteger 2 * n3)) : Stream Nat -> Stream Nat
-- TODONOTE "Also, the Monad Stream instance is like the Vect one, it zips, since appending makes no sense with infinite Streams."
-- TODONOTE credit Melvar for this information
-- TODONOTE :t\ns : List Nat => [ 2 * n | n <- ns, ((mod n 2) == 0) ] 
-- TODONOTE \ns =>
-- TODONOTE        ns >>=
-- TODONOTE            \n =>
-- TODONOTE                     guard (mod n (fromInteger 2) == fromInteger 0) >>=
-- TODONOTE                           \{bindx0} => return (fromInteger 2 * n) : List Nat -> List Nat

-- TODONOTE see discussion in TUOLP.idr about options for creating "streams" because they lack Alternative instances (unrolling comprehensions into do notation, then filtering on a sentinel)
{-                           
evens3 : Stream Nat
evens3 = [ 2*n | n <- naturals, True ]

evens1 : Stream Nat
evens1 = [ n | n <- naturals , ((mod n 2) == 0)]

odds1 =  [ n | n <- naturals , odd n ]

small_squares2 = [ n*n | n <- naturals , n < 1000 ]
-}

run : Integer -> List Integer
run 1 = [1]
run n = case (mod n 2) == 0 of
             True  => n :: run (div n 2)
             False => n :: run (3*n + 1)

ones : Stream Nat
ones = 1 :: ones

characters : List String
characters = nub [ x    | ["play",_,_,x]  <- db ]

movies : List String
movies     =     [ x    | ["release",x,_] <- db ]

actors : List String
actors     = nub [ x    | ["play",x,_,_]  <- db ]

directors : List String
directors  = nub [ x    | ["direct",x,_]  <- db ]

dates : List String
dates      = nub [ x    | ["release",_,x] <- db ]

universe : List String
universe   = nub (characters++actors++directors++movies++dates)

direct : List (String, String)
direct     = [ (x,y)   | ["direct",x,y]  <- db ]
act : List (String, String)
act        = [ (x,y)   | ["play",x,y,_]  <- db ]
play : List (String, String, String)
play       = [ (x,y,z) | ["play",x,y,z]  <- db ]
release : List (String, String)
release    = [ (x,y)   | ["release",x,y] <- db ]

charP : String -> Bool
charP       = \x       => elem x characters 

actorP : String -> Bool
actorP      = \x       => elem x actors

movieP : String -> Bool
movieP      = \x       => elem x movies 

directorP : String -> Bool
directorP   = \x       => elem x directors

dateP : String -> Bool
dateP       = \x       => elem x dates 

actP : (String,String) -> Bool
actP        = \(x,y)   => elem (x,y) act

releaseP : (String,String) -> Bool
releaseP    = \(x,y)   => elem (x,y) release 

directP : (String,String) -> Bool
directP     = \(x,y)   => elem (x,y) direct 

playP : (String, String, String) -> Bool
playP       = \(x,y,z) => elem (x,y,z) play

q1 : List String
q1 = [ x | x <- actors, directorP x ] 

q2 : List (String, String)
q2 = [ (x,y) | (x,y) <- act, directorP x ]

q3 : List (String, String, String)
q3 = [ (x,y,z) | (x,y) <- direct, (y,z) <- release ]

q4 : List (String, String, String)
q4 = [ (x,y,z) | (x,y) <- direct, (u,z) <- release, y == u ]

q5 : List (String, String)
q5 = [ (x,y) | (x,y) <- direct, (u,"1995") <- release, y == u ]

q6 : List (String, String, String)
q6 = [ (x,y,z) | (x,y) <- direct, (u,z) <- release, 
                  y == u, z > "1995"                           ]

q7 : List (String)
q7 = [ x | ("Kevin Spacey",x) <- act ]

q8 : List String
q8 = [ x | (x,y) <- release, y > "1997", actP ("William Hurt",x) ]

q9 : Bool
q9 = q1 /= []

-- TODONOTE can't do this one directly
q10_q : List String
q10_q = [x | ("Woody Allen",x) <- direct]

q10 : Bool 
q10 = q10_q /= []

q10' : Bool
q10' = directorP "Woody Allen" 

elem' : Eq a => a -> List a -> Bool
elem' x  []                 = False
elem' x  (y::ys) = if x == y then True else  elem' x ys

addElem : a -> List (List a) -> List (List a)
addElem x = with List map (x ::) 

powerList  : List a -> List (List a)
powerList  [] = [[]]
powerList  (x::xs) = (powerList xs) ++ (map (x::) (powerList xs))

orderedSubsets : (Eq a) => List a -> List (List a)
orderedSubsets xs = let ps = powerList xs in
                        filter (\x => isPrefixOf x xs) ps

-- TODONOTE not sure the intent of this method, need to refer to the text
{-
data S = Void deriving (Eq,Show)
empty : [S]
empty = []
-}


--display' : Int -> Int -> List Char 
--display' n m Nil = with List Char []
--display' n m (x::xs) = if  n == m then  '\n':: display'  n   0  (x::xs) else
 --                                         x  :: display'  n (m+1)  xs 
{-
display : Int -> String -> IO ()
display n str = putStrLn (pack (display' n 0 (unpack str)))
-}
