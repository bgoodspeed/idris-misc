module LTE

import Syntax.PreOrderReasoning

%default total


qed : (n : Nat) -> LTE n n
qed Z = LTEZero 
qed (S k) = LTESucc (qed k) 

step : (i : Nat) -> LTE i j -> LTE j k -> LTE i k
step Z x x1 = LTEZero
step (S k) (LTESucc x) (LTESucc y) = LTESucc (step k x y) 


test0 : LTE 1 1
test0 = LTESucc LTEZero





test1a : LTE 1 2
test1a = LTESucc LTEZero

test1b : LTE 1 3
test1b = LTESucc LTEZero

test1c : LTE 1 4
test1c = LTESucc LTEZero

test1' : LTE 1 4
test1' = 1 ={ (LTESucc LTEZero) }=
         2 ={ (LTESucc (LTESucc LTEZero)) }=
         3 ={ (LTESucc (LTESucc (LTESucc LTEZero))) }=
         4 QED


test1 : LTE 1 4 
test1 = 1 ={ LTESucc LTEZero }= 
        2 ={ LTESucc (LTESucc LTEZero) }= 
        4 QED

