module NonDet where

import Free
import Hefty
import Handler

import Control.Monad (liftM2)

data NonDet k where
    Empty :: NonDet k
    Choice :: (Bool -> k) -> NonDet k
    deriving Functor

empty :: NonDet < f => Free f a
empty = Op $ inj Empty

choice :: NonDet < f => Free f Bool
choice = Op $ inj $ Choice Pure

hNonDet :: Functor f => Handler NonDet a f [a]
hNonDet = Handler {
    ret = \a -> pure [a],
    hdlr = \case
        Empty -> pure []
        Choice k -> liftM2 (++) (k False) (k True)
}

handleNonDet :: Functor f => Free (NonDet + f) a -> Free f [a]
handleNonDet = handle hNonDet

liftNonDet :: Alg NonDet <: h => Free NonDet a -> Hefty h a
liftNonDet = lift