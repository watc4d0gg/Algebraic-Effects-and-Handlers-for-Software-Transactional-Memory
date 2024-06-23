module Main where

import Free
import STM
import Thread

import Prelude hiding (lookup, log)

transactTest :: IO ()
transactTest = runProg $ do
    acc <- atomically $ do newTVar 0
    fork $ atomically $ limitedWithdraw acc 42
    fork $ atomically $ writeTVar acc 1337
    where
        limitedWithdraw :: STM < f => TVar Int -> Int -> Free f ()
        limitedWithdraw acc amount = do
            bal <- readTVar acc
            check (amount <= 0 || amount <= bal)
            writeTVar acc (bal - amount)

main :: IO ()
main = transactTest