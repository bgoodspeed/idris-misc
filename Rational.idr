module Rational

-- TODONOTE there is no rational class
-- TODONOTE could use a type class, but whatever
Rational : Type
Rational = (Integer, Integer)


quotRem : Integer -> Integer -> (Integer, Integer)
quotRem n d = (div n d, mod n d)

numerator : Rational -> Integer
numerator (n,d) = n

denominator : Rational -> Integer
denominator (n,d) = d 

--TODONOTE we don't have % to construct a ratio (which also doesn't exist
--TODONOTE x < 0 error,  
decExpand : Rational -> List Integer
decExpand x = let n     = numerator x 
                  d     = denominator x 
                  (q,r) = quotRem n d
                  r10   = r * 10
                in
              if r == 0 then [q] else q :: decExpand( quotRem r10 d) 

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
recip (n,d) = (d,n)

rationalMult : Rational -> Rational -> Rational
rationalMult (x,y) (n,m) = (x*n, y*m)

rationalAdd : Rational -> Rational -> Rational
rationalAdd (x,y) (n,m) = (m*x + n*y, m*y)
                              

