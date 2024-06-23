module State where

import Free
import Handler
import Hefty

data State s k where
    Get :: (s -> k) -> State s k
    Put :: s -> k -> State s k
    deriving Functor

get :: State s < f => Free f s
get = Op $ inj $ Get Pure

put  :: State s < f => s -> Free f ()
put s = Op $ inj $ Put s (Pure ())

hState :: Functor f => StatefulHandler (State s) a s f (a, s)
hState = StatefulHandler {
    retS = curry pure,
    hdlrS = \x s -> case x of
        Put s' k -> k s'
        Get k -> k s s
}

handleState :: Functor f => s -> Free (State s + f) a -> Free f (a, s)
handleState = handleStateful hState

get' :: Alg (State s) <: h => Hefty h s
get' = injAlg $ Get Return

put' :: Alg (State s) <: h => s -> Hefty h ()
put' s = injAlg $ Put s (Return ())
