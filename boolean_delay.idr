module Main

anyAndDelayFalseIsFalse : (b : Bool) -> b && False = False
anyAndDelayFalseIsFalse b = ?anyAndDelayFalseIsFalse_rhs1

anyIntAndIntToBoolAndDelayFalseIsFalse : (i : Int) -> (intToBool i) && False = False
anyIntAndIntToBoolAndDelayFalseIsFalse i = ?anyIntAndIntToBoolAndDelayFalseIsFalse_rhs




---------- Proofs ----------

Main.anyAndDelayFalseIsFalse_rhs1 = proof
  intros
  case b
  trivial
  trivial


Main.anyIntAndIntToBoolAndDelayFalseIsFalse_rhs = proof
  intros
  case intToBool i
  trivial
  trivial


