{-# LANGUAGE UndecidableInstances #-}
module STM where

import Free
import Handler
import State
import Out
import NonDet
import Hefty
import Thread

import Prelude hiding (lookup)
import Control.Monad (unless)
import Unsafe.Coerce (unsafeCoerce)

data Cell = forall a. (Show a, Eq a) => Cell a

deriving instance Show Cell

instance Eq Cell where
    (==) :: Cell -> Cell -> Bool
    Cell a == Cell b = show a == show b

newtype TVar a = TVar Int
    deriving (Eq, Show)

type Heap = [Cell]

alloc :: (Show a, Eq a) => a -> Heap -> (TVar a, Heap)
alloc a h = (TVar (length h), h ++ [Cell a])

update :: (Show a, Eq a) => TVar a -> a -> Heap -> Heap
update _ _ [] = undefined
update (TVar i) a (c : cs)
    | i == 0    = Cell a : cs
    | otherwise = c : update (TVar $ i - 1) a cs

lookup :: (Show a, Eq a) => TVar a -> Heap -> a
lookup _ [] = undefined
lookup (TVar i) (Cell a : cs)
    | i == 0    = unsafeCoerce a
    | otherwise = lookup (TVar $ i - 1) cs

data STM k where
    New     :: (Show a, Eq a) => a -> (TVar a -> k) -> STM k
    Read    :: (Show a, Eq a) => TVar a -> (a -> k) -> STM k
    Write   :: (Show a, Eq a) => TVar a -> a -> k -> STM k
    Retry   :: STM k
    OrElse  :: k -> k -> STM k

deriving instance Functor STM

newTVar :: (Show a, Eq a, STM < f) => a -> Free f (TVar a)
newTVar a = Op $ inj $ New a Pure

readTVar :: (Show a, Eq a, STM < f) => TVar a -> Free f a
readTVar t = Op $ inj $ Read t Pure

writeTVar :: (Show a, Eq a, STM < f) => TVar a -> a -> Free f ()
writeTVar t a = Op $ inj $ Write t a (Pure ())

retry :: STM < f => Free f a
retry = Op $ inj Retry

check :: STM < f => Bool -> Free f ()
check b = unless b retry

orElse :: STM < f => Free f a -> Free f a -> Free f a
orElse t1 t2 = Op $ inj $ OrElse t1 t2

-- Single-threaded STM handler
hSTM :: Functor f => StatefulHandler STM a Heap f (Maybe (a, Heap))
hSTM = StatefulHandler {
    retS = \a h -> return $ Just (a, h),
    hdlrS = \op h -> case op of
        New a k -> let (t, h') = alloc a h in k t h'
        Read t k -> let a = lookup t h in k a h
        Write t a k -> k $ update t a h
        Retry -> return Nothing
        OrElse t1 t2 -> t1 h >>= maybe (t2 h) (return . Just)
}

handleSTM :: Functor f => Heap -> Free (STM + f) a -> Free f (Maybe (a, Heap))
handleSTM = handleStateful hSTM

atomically :: (Thread <: h, Alg (State Heap) <: h) => Free (STM + End) a -> Hefty h a
atomically t = do
    initial <- get'
    let eval = un $ handleSTM initial t
    case eval of
        Just (a, changed) -> do
            commit <- atomic $ do
                current <- get'
                if current == initial then
                    put' changed >> return True
                else
                    return False
            if commit then return a else atomically t
        Nothing -> atomically t

type Prog a = Hefty (Thread :+: Alg (State Heap) :+: Alg Err :+: Alg Out) a

runProg :: Show a => Prog a -> IO ()
runProg prog = do
    r <- io
        $ handleError
        $ handleState ([] :: Heap)
        $ hfold Pure (eAlg /\ eAlg /\ eAlg)
        $ execute prog
    print r

runAllExecutions :: Show a => Hefty (Thread :+: Alg (State Heap) :+: Alg Err :+: Alg NonDet :+: Alg Out) a -> IO ()
runAllExecutions prog = do
    r <- io
        $ handleNonDet
        $ handleError
        $ handleState ([] :: Heap)
        $ hfold Pure (eAlg /\ eAlg /\ eAlg /\ eAlg)
        $ executeAll prog
    print r
