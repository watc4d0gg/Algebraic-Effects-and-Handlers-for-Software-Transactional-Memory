module Philosophers where

import Free
import State
import STM
import Out
import Hefty
import Thread

import Control.Monad (forever)
import Prelude hiding (putStrLn)

-- Necessary TMVar boilerplate (https://hackage.haskell.org/package/stm-2.5.3.1/docs/src/Control.Concurrent.STM.TMVar.html)
data TMVar a = (Show a, Eq a) => TMVar (TVar (Maybe a))

newTMVar :: (Show a, Eq a, STM < f) => a -> Free f (TMVar a)
newTMVar a = do
    t <- newTVar $ Just a
    return $ TMVar t

takeTMVar :: STM < f => TMVar a -> Free f a
takeTMVar (TMVar t) = do
    m <- readTVar t
    case m of
        Nothing -> retry
        Just a  -> writeTVar t Nothing >> return a

putTMVar :: STM < f => TMVar a -> a -> Free f ()
putTMVar (TMVar t) a = do
    m <- readTVar t
    case m of
        Nothing -> writeTVar t $ Just a
        Just _  -> retry

-- Adaptiation of Dining Philosophers solution from RosettaCode to algebraic effects (https://rosettacode.org/wiki/Dining_philosophers#Haskell)
type Fork = TMVar Int

newFork :: (Thread <: h, Alg (State Heap) <: h, Alg Err <: h, Alg Out <: h) => Int -> Hefty h Fork
newFork i = atomically $ do newTMVar i

-- The basic transactional operations on forks
takeFork :: STM < f => Fork -> Free f Int
takeFork = takeTMVar

releaseFork :: STM < f => Int -> Fork -> Free f ()
releaseFork = flip putTMVar

type Name = String

putStrLn :: Alg Out <: h => String -> Hefty h ()
putStrLn = liftOut . out

threadDelay :: (Thread <: h, Alg Out <: h) => Int -> Hefty h ()
threadDelay = wait

randomRIO :: Alg Out <: h => (Int, Int) -> Hefty h Int
randomRIO = liftOut . uncurry random

runPhilosopher :: (Thread <: h, Alg (State Heap) <: h, Alg Err <: h, Alg Out <: h) => Name -> (Fork, Fork) -> Hefty h ()
runPhilosopher name (left, right) = forever $ do
    putStrLn (name ++ " is hungry.")
    
    (leftNum, rightNum) <- atomically $ do
        leftNum <- takeFork left
        rightNum <- takeFork right
        return (leftNum, rightNum)

    putStrLn (name ++ " got forks " ++ show leftNum ++ " and " ++ show rightNum ++ " and is now eating.")
    delay <- randomRIO (1,10)
    threadDelay (delay * 1000000) -- 1, 10 seconds
    putStrLn (name ++ " is done eating. Going back to thinking.")

    atomically $ do
        releaseFork leftNum left
        releaseFork rightNum right

    delay <- randomRIO (1,10)
    threadDelay (delay * 1000000)

philosophers :: [Name]
philosophers = ["Aristotle", "Kant", "Spinoza", "Marx", "Russel"]

runPhilosophers :: Prog ()
runPhilosophers = do 
    forks <- mapM newFork [1..5]
    let namedPhilosophers     = map runPhilosopher philosophers
        forkPairs             = zip forks (tail . cycle $ forks)
        philosophersWithForks = zipWith ($) namedPhilosophers forkPairs
    putStrLn "Running the philosophers. Press Ctrl-C to quit."
    mapM_ fork philosophersWithForks