module GS 

import Debug.Error

import Utilities
import Rational

rem : Integer -> Integer -> Integer
rem = mod

-- TODONOTE  funcname :: Arg -> Arg2 -> ReturnType in haskell is
--           funcname  : Arg -> Arg2 -> ReturnType in idris

divides : Integer -> Integer -> Bool
divides d n = rem n d == 0


-- TODONOTE we don't have | for conditional pattern matching in idris
-- we have if .. then .. else and case ... of .. => ..
-- we don't have ^2 as exponentiation, use k*K
ldf' : Integer -> Integer -> Integer
ldf' k n = case divides k n of
                True  => k
                False => case (k*k) > n of 
                              True => n
                              False => ldf' (k+1) n
                
--TODONOTE we don't ahve | for cond matching without using a "with" construct, but we can do compare and match on LT GT etc





ld : Integer -> Integer 
ld n = ldf' 2 n 


-- TODONOTE we need to return the correct type, and we can't give the correct type to error (or can we?)  either way 
-- TODO need to figure out how to abor
prime0 :(k : Integer) -> {auto ok : (k >= 0) = True  }-> Bool
prime0 n = case compare n 1 of
                EQ  => False
                _   => ld n == n


--TODONOTE here we use augmented pattern matching "with" syntax
prime0' : (k : Integer) -> Bool
prime0' k with (k == 1)
  | True  = False
  | False = ld k == k


-- TODONOTE concat in lists is :: in idris not : (they are swapped)
-- TODO need to figure out this function
{-
mnmInt : (l : List Int) -> So (isCons l) -> Int
mnmInt (x :: Nil) pf = x
mnmInt (x :: xs) pf = min x (mnmInt xs Oh )
-}
{-
mnmInt : (l : List Int) -> {auto ok: isCons l = True} -> Int
mnmInt (x :: Nil) = x
mnmInt (x :: xs ) {pf}  = min x (mnmInt xs ?foo)
-}

mnmIntNonTotal : List Int -> Int
mnmIntNonTotal [x] = x
mnmIntNonTotal (x :: (y :: xs)) = let mi = mnmIntNonTotal (y :: xs) in
                                      min x mi

mnmInt : List Int -> Maybe Int
mnmInt [] = Nothing
mnmInt (x :: []) = Just x
mnmInt (x :: (y :: xs)) = let mi = mnmInt (y :: xs) in
                              case mi of 
                                   Nothing => Just x
                                   Just a  => Just (min x a)

-- TODONOTE no | for pattern matching, maybe via with
min' : Int -> Int -> Int 
min' x y = if  x <= y then x else y

-- TODONOTE there is no Rational type in idris, we create one as a pair (n,d)
average : List Integer -> Rational 
average [] = error "empty list" 
average xs = (sum xs,  cast (length xs))

-- TODONOTE need to specify which [] syntax we mean, vect, list etc
sum' : List Int -> Int
sum' [] = 0 
sum' (x::xs) = x + sum' xs

-- TODONOTE need to give it a type param {a : Type} -> ...
length' : {a : Type} -> List a -> Int
length' [] = 0 
length' (x::xs) = 1 + length' xs


-- TODONOTE can't use the name prefix because it is a reserved word (like infix etc, as a syntax hint)
-- TODONOTE can't pattern match on strings
isPrefix : String -> String -> Bool
isPrefix s1 s2 = isPrefixList (unpack s1) (unpack s2) where
  isPrefixList : List Char -> List Char -> Bool 
  isPrefixList [] ys = True
  isPrefixList (x::xs) [] = False
  isPrefixList (x::xs) (y::ys) = (x==y) && isPrefixList xs ys 


-- TODONOTE in haskell you can say foo x where x = f(y), in idris where is used only for defining aux functions in the block, we need to use let beforehand for a similar behavior

factors : Integer -> List Integer
factors n = case compare n 1 of
                 LT   => [] 
                 EQ   => []
                 _    => let p = ld n in p :: factors (div n p) 


-- TODONOTE haskell is lazy by default, to get that behavior we need to use Lazy
-- TODONOTE we can use Stream a for infinite streams, but we don't get filter (because we don't know it will return true infinitely many times)
primes0 : Stream Integer
primes0 = filterStream prime0' [2..]    

-- TODONOTE More pattern matching, ugly nested if/else block
ldpf : List Integer -> Integer -> Integer
ldpf (p::ps) n = if rem n p == 0 then p else 
                    if (p*p) > n then n else ldpf ps n

ldpfStream : Stream Integer -> Integer -> Integer
ldpfStream (p::ps) n = if rem n p == 0 then p else
                          if (p*p) > n then n else ldpfStream ps n


-- TODONOTE need to explicitly declare mutual blocks 
-- TODONOTE we can put these checks for error conds into the dependent type sigs
-- TODO use So() or {auto ok : P(n) = True } etc.
-- TODO need to figure out streams before this block is workable
mutual
  prime : Integer -> Bool
  prime n = case compare n 1 of 
               LT => False -- TODO should be able use So() or proof search
               EQ => False
               _  => (ldp n) == n


  -- TODONOTE we have the same sugar for infinite lists [3..]
  -- TODO need to confirm if this is lazy though
  primes1 : Stream Integer
  primes1 = 2 :: filterStream prime [3..]

  ldp : Integer -> Integer
  ldp n = ldpfStream primes1 n
-- TODO [3..] is a Stream type, need to do voodoo to it to call it a list?

-- TODONOTE a,b need type declarations
a : Integer
a = 3

b : Integer
b = 4 
f : Integer -> Integer -> Integer
f x y = x*x + y*y

g : Integer -> Integer 
g 0     = 1
g x = 2 * g (x-1)

h1 : Integer -> Integer 
h1 0 = 0
h1 x = 2 * (h1 x) 

h2 : Integer -> Integer 
h2 0 = 0
h2 x = h2 (x+1) 

