module Rational

-- TODONOTE there is no rational class
-- TODONOTE could use a type class, but whatever

data Rational : Type where
  MkRational : Nat -> (d : Nat) -> GT d Z -> Rational



quotRem : Nat -> Nat -> (Nat, Nat)
quotRem n d = (div n d, mod n d)

numerator : Rational -> Nat
numerator (MkRational x d prf) = x


denominator : Rational -> Nat
denominator (MkRational x d prf) = d

{- TODONOTE elemIndex is confused about (Int vs Nat), there's no cast tho?
-}
decF : Nat -> Nat -> List (Nat,Nat) -> (List Nat, List Nat)
decF n d xs = let   (q,r)  = quotRem n d
                    xs'     = reverse xs
                    (Just k)  = elemIndex (q,r) xs'
                    (ys,zs) = splitAt k (map fst xs') in
               if r == 0 then (reverse (q :: (map fst xs)),[]) else
                  if elem (q,r) xs then (ys,zs) else 
                      decF (r*10) d ((q,r)::xs)
-- TODONOTE handle x < 0 error
decForm : Rational -> (Nat,List Nat, List Nat) 
decForm x = let  
                  n       = numerator x 
                  d       = denominator x 
                  (q,r)   = quotRem n d 
                  (ys,zs) = decF (r*10) d [] in
                  (q, ys, zs)


recip : Rational -> Rational
recip (MkRational Z d prf) = MkRational Z (S Z) (LTESucc LTEZero)
recip (MkRational (S k) d prf) = MkRational d (S k) (LTESucc LTEZero) 

rationalMult : Rational -> Rational -> Rational
rationalMult (MkRational x Z prf) (MkRational y Z w) = absurd prf
rationalMult (MkRational x Z prf) (MkRational y (S k) w) = absurd prf 
rationalMult (MkRational x (S k) prf) (MkRational y Z w) = absurd w
rationalMult (MkRational x (S k) prf) (MkRational y (S l) w) = MkRational (x * y) ((S k) * (S l)) (LTESucc LTEZero)



rationalAdd : Rational -> Rational -> Rational
rationalAdd (MkRational x Z p1) (MkRational n Z p2) = absurd p1
rationalAdd (MkRational x Z p1) (MkRational n (S k) p2) = absurd p1
rationalAdd (MkRational x (S k) p1) (MkRational n Z p2) = absurd p2
rationalAdd (MkRational x (S k) p1) (MkRational n (S l) p2) = 
  MkRational ((x * (S l)) + (n * (S k))) ((S k) * (S l)) (LTESucc LTEZero)
                              

