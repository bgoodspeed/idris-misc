module Polynomials 

--TODONOTE we don't ahve default likethis, figure out what that means in haskell
--default (Integer, Rational, Double) 

infixl 7 .*
(.*) : Num a => a -> List a -> List a
c .* []     = []
c .* (f::fs) = c*f :: (c .* fs)

z : (Num a, Neg a) => List a
z = [0,1]

--TODONOTE this is in the Num class in haskell but separate here
instance (Num a, Ord a, Neg a) => Neg (List a) where
  negate []       = []
  negate (f::fs)   = (negate f) :: (negate fs)

mutual
  signum' : (Num a, Ord a, Neg a) => a -> a
  signum' x = case compare x 0 of
                   LT  => negate 1
                   EQ  => 0
                   _   => 1

  signum : (Num a, Ord a, Neg a) => List a -> List a
  signum [] = []
  signum (g::gs) = let lst = last (g :: gs) 
                       sgn = signum' lst in
                        if sgn < (fromInteger 0) then negate z else z


  --TODONOTE the Num class does not define signum
  instance (Num a,Ord a, Neg a) => Num (List a) where
    fromInteger c   = [fromInteger c] 
    abs gs = if signum gs == z then gs else negate gs
    abs [] = []

   

    fs     - []     = fs
    []     - gs     = gs
    (f::fs) - (g::gs) = f-g :: fs-gs

    fs     + []     = fs
    []     + gs     = gs
    (f::fs) + (g::gs) = f+g :: fs+gs
    fs     * []     = []
    []     * gs     = []
    (f::fs) * (g::gs) = f*g :: (f .* gs + fs * (g::gs))


delta : (Neg a, Num a, Ord a) => List a -> List a
delta = ([1,-1] *)

shift : List a -> List a
shift [] = []
shift (x::xs) = xs

p2fct : Num a => List a -> a -> a
p2fct [] x = 0
p2fct (a::as) x = a + (x * p2fct as x)

-- TODONOTE can't pattern match on 0::gs then match on g::gs next, TODO confirm see why?
-- TODONOTE error _ [] should have msg ".."
comp : (Eq a,Num a,Ord a, Neg a) => List a -> List a -> List a
comp []     _      = []
comp (f::fs) (g::gs) = if g == 0 then  f :: gs * (comp fs (0::gs)) else
                         ([f] + [g] * (comp fs (g::gs))) + (0 :: gs * (comp fs (g::gs)))

deriv : Num a => List a -> List a
deriv []     = []
deriv (f::fs) = deriv1 fs 1 where 
  deriv1 []     _ = []
  deriv1 (g::gs) n = n*g :: deriv1 gs (n+1)

