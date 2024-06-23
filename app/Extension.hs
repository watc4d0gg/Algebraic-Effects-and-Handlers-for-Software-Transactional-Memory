module Extension where

import Hefty
import Free
import Handler
import State
import STM (Heap, TVar, alloc, lookup, update)
import Thread
import Prelude hiding (lookup)
import Writer
import Out

data Transactional k where
    Retry :: Transactional k
    OrElse :: k -> k -> Transactional k
    deriving Functor

retry :: Transactional < f => Free f a
retry = Op $ inj Retry

orElse :: Transactional < f => Free f a -> Free f a -> Free f a
orElse t1 t2 = Op $ inj $ OrElse t1 t2

hTransactional :: Functor f => Handler Transactional a f (Maybe a)
hTransactional = Handler {
    ret = pure . Just,
    hdlr = \case
        Retry -> return Nothing
        OrElse t1 t2 -> t1 >>= maybe t2 (return . Just)
}

data TMemory k where
    NewTVar :: (Show a, Eq a) => a -> (TVar a -> k) -> TMemory k
    ReadTVar :: (Show a, Eq a) => TVar a -> (a -> k) -> TMemory k
    WriteTVar :: (Show a, Eq a) => TVar a -> a -> k -> TMemory k

deriving instance Functor TMemory

newTVar' :: (Show a, Eq a, TMemory < f) => a -> Free f (TVar a)
newTVar' a = Op $ inj $ NewTVar a Pure

readTVar' :: (Show a, Eq a, TMemory < f) => TVar a -> Free f a
readTVar' t = Op $ inj $ ReadTVar t Pure

writeTVar' :: (Show a, Eq a, TMemory < f) => TVar a -> a -> Free f ()
writeTVar' t a = Op $ inj $ WriteTVar t a (Pure ())

hTMemory :: Functor f => StatefulHandler TMemory a Heap f (a, Heap)
hTMemory = StatefulHandler {
    retS = curry pure,
    hdlrS = \op h -> case op of
        NewTVar a k -> let (t, h') = alloc a h in k t h'
        ReadTVar t k -> let a = lookup t h in k a h
        WriteTVar t a k -> k $ update t a h
}

atomically' :: (Eq w, Functor f, Thread <: h, Alg (State w) <: h, Alg Out <: h) => (forall f'. Functor f' => StatefulHandler f a w f' (a, w)) -> Free (f + Transactional + End) a -> Hefty h a
atomically' h t = do
    initial <- get'
    let eval = un $ handle hTransactional $ handleStateful h initial t
    case eval of
        Just (a, changed) -> do
            commit <- atomic $ do
                current <- get'
                if current == initial then
                    put' changed >> return True
                else
                    return False
            if commit then return a else atomically' h t
        Nothing -> atomically' h t

atomicallySTM :: (Thread <: h, Alg (State Heap) <: h, Alg Out <: h) => Free (TMemory + Transactional + End) a -> Hefty h a
atomicallySTM = atomically' hTMemory

atomicallyWriter :: (Eq m, Monoid m, Thread <: h, Alg (State m) <: h, Alg Out <: h) => Free (Writer m + Transactional + End) a -> Hefty h a
atomicallyWriter = atomically' hWriter
