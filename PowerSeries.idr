module PowerSeries 


import Polynomials 

--default (Integer, Rational, Double) 
--TODONOTE we don't have a fractional type class, need to add that and ratio
{-
instance (Ord a, Fractional a) => Fractional [a] where
  fromRational c  = [fromRational c] 
  fs     / []     = error "division by 0 attempted"
  []     / gs     = []
  (0:fs) / (0:gs) = fs / gs 
  (_:fs) / (0:gs) = error "division by 0 attempted"
  (f:fs) / (g:gs) = let q = f/g in 
       q : (fs - q.*gs) / (g:gs)
       -}

-- TODONOTE fractional guard needed on a instead of Float
int : List Float -> List Float 
int fs = 0 :: int1 fs 1 where 
  int1 : List Float -> Float -> List Float
  int1 []     _ = []
  int1 (g::gs) n = g/n :: (int1 gs (n+1))


expz : (List Float)
expz = 1 + (int expz) 
