module StateUtils

import Control.Monad.Identity
import Control.Monad.State


runState : State s a -> s -> (a, s)
runState m = runIdentity . runStateT m 


evalState : State s a -> s -> a
evalState m s = fst (runState m s)  


