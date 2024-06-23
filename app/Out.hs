module Out where

import Free hiding (type(+))
import Hefty

import System.CPUTime (getCPUTime)
import System.Random (randomRIO)

data Out k where
    Out     :: String -> k -> Out k
    Time    :: (Int -> k) -> Out k
    Random  :: Int -> Int -> (Int -> k) -> Out k
    deriving Functor

out :: Out < f => String -> Free f ()
out s = Op $ inj $ Out s (Pure ())

time :: Out < f => Free f Int
time = Op $ inj $ Time Pure

random :: Out < f => Int -> Int -> Free f Int
random low high = Op $ inj $ Random low high Pure

io :: Free Out a -> IO a
io = fold return (\case
    Out s k -> putStrLn s >> k
    Time k -> getCPUTime >>= k . fromInteger . (`div` 1000000)    -- from picoseconds to microseconds
    Random low high k -> randomRIO (low, high) >>= k)

liftOut :: Alg Out <: h => Free Out a -> Hefty h a
liftOut = lift