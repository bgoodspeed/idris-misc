module Rational

-- TODONOTE there is no rational class
-- TODONOTE could use a type class, but whatever

data Rational : Type where
  MkRational : Integer -> (d : Integer) -> ((d == 0) = False) -> Rational


quotRem : Integer -> Integer -> (Integer, Integer)
quotRem n d = (div n d, mod n d)

numerator : Rational -> Integer
numerator (MkRational x d prf) = x


denominator : Rational -> Integer
denominator (MkRational x d prf) = d

{- TODONOTE elemIndex is confused about (Int vs Integer), there's no cast tho?
-}
decF : Integer -> Integer -> List (Integer,Integer) -> (List Integer, List Integer)
decF n d xs = let   (q,r)  = quotRem n d
                    xs'     = reverse xs
                    (Just k)  = elemIndex (q,r) xs'
                    (ys,zs) = splitAt k (map fst xs') in
               if r == 0 then (reverse (q :: (map fst xs)),[]) else
                  if elem (q,r) xs then (ys,zs) else 
                      decF (r*10) d ((q,r)::xs)
-- TODONOTE handle x < 0 error
decForm : Rational -> (Integer,List Integer, List Integer) 
decForm x = let  
                  n       = numerator x 
                  d       = denominator x 
                  (q,r)   = quotRem n d 
                  (ys,zs) = decF (r*10) d [] in
                  (q, ys, zs)


recip : Rational -> Rational
recip (MkRational x d prf) = case x == 0 of
                                  True => MkRational 0 1 Refl
                                  False => MkRational d x ?pfInverse

rationalMult : Rational -> Rational -> Rational
rationalMult (MkRational x d prf) (MkRational y z w) = MkRational (x*y) (d*z) ?pfMult 

rationalAdd : Rational -> Rational -> Rational
rationalAdd (MkRational x y p1) (MkRational n m p2) = MkRational (m*x + n*y) (m*y) ?pfAdd
                              

