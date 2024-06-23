module Writer where

import Free
import Handler
import Hefty

data Writer m k where
    Tell :: m -> k -> Writer m k
    deriving Functor

tell :: Writer m < f => m -> Free f ()
tell m = Op $ inj $ Tell m (Pure ())

hWriter :: (Monoid m, Functor f) => StatefulHandler (Writer m) a m f (a, m)
hWriter = StatefulHandler {
    retS = curry pure,
    hdlrS = \(Tell m' k) m -> k $ m <> m'
}

handleWriter :: (Monoid m, Functor f) => m -> Free (Writer m + f) a -> Free f (a, m)
handleWriter = handleStateful hWriter

tell' :: Alg (Writer m) <: h => m -> Hefty h ()
tell' m = injAlg $ Tell m (Return ())