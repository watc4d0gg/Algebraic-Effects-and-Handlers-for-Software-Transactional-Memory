module Thread where

import Free
import Hefty
import Out
import NonDet

import GHC.Base (join)
import Data.List (permutations)
import Data.Functor ((<&>))

data Thread h k where
    Atomic :: h a -> (a -> k) -> Thread h k
    Fork :: h a -> k -> Thread h k
    Wait :: Int -> k -> Thread h k

deriving instance Functor (Thread h)

instance HFunctor Thread where
    hmap :: (f ~> g) -> Thread f ~> Thread g
    hmap f (Atomic m k) = Atomic (f m) k
    hmap f (Fork m k) = Fork (f m) k
    hmap _ (Wait d k) = Wait d k

    weave :: (Monad m, Monad n, Functor s) => s () -> (forall x. s (m x) -> n (s x)) -> Thread m (m a) -> Thread n (n (s a))
    weave s f (Atomic m k) = Atomic (f $ m <$ s) (f . fmap k)
    weave s f (Fork m k) = Fork (f $ m <$ s) (f $ k <$ s)
    weave s f (Wait d k) = Wait d (f $ k <$ s)

atomic :: Thread <: h => Hefty h a -> Hefty h a
atomic a = Do $ injH $ Atomic a Return

fork :: Thread <: h => Hefty h a -> Hefty h ()
fork w = Do $ injH $ Fork w (Return ())

wait :: (Alg Out <: h, Thread <: h) => Int -> Hefty h ()
wait delay = liftOut time >>= \t -> Do $ injH $ Wait (t + delay) (Return ())

data Worker h = forall x. Worker (Hefty (Thread :+: h) x)

data ThreadState h a where
    Active :: a -> ThreadState h a
    Yielded :: Hefty (Thread :+: h) a -> ThreadState h a
    Forked :: Worker h -> Hefty (Thread :+: h) a -> ThreadState h a

deriving instance HFunctor h => Functor (ThreadState h)

runThread :: (Alg Err <: h, Alg Out <: h) => Hefty (Thread :+: h) a -> Hefty h (ThreadState h a)
runThread (Return a) = return $ Active a
runThread (Do op) = case op of
    HL h -> case h of
        Atomic a k -> runAtomic a <&> (Yielded . k)
        Fork w k -> return $ Forked (Worker w) k
        Wait d k -> do
            t <- liftOut time
            if t >= d then runThread k else return $ Yielded (Do op)
    HR h -> Do $ weave (Active ()) suspend h

runAtomic :: Alg Err <: h => Hefty (Thread :+: h) a -> Hefty h a
runAtomic (Return a) = return a
runAtomic (Do op) = case op of
    HL _ -> liftErr $ err "Calling thread operations inside atomic!"
    HR h -> do
        s <- Do $ weave (Active ()) suspend h
        case s of
            Active a -> return a
            Yielded m -> runAtomic m
            _ -> liftErr $ err "Calling thread operations inside atomic!"

suspend :: HFunctor h => ThreadState h (Hefty (Thread :+: h) a) -> Hefty h (ThreadState h a)
suspend (Active op) = case op of
    Return a -> return $ Active a
    _ -> return $ Yielded op
suspend (Yielded k) = return $ Yielded (join k)
suspend (Forked w k) = return $ Forked w (join k)

-- real scheduler
execute :: (Alg Err <: h, Alg Out <: h) => Hefty (Thread :+: h) a -> Hefty h a
execute t = main t []
    where
        main :: (Alg Err <: h, Alg Out <: h) => Hefty (Thread :+: h) a -> [Worker h] -> Hefty h a
        main m ws = do
            s <- runThread m
            case s of
                Active a    -> if null ws then return a else workers ws [] (return a)
                Yielded k   -> workers ws [] k
                Forked w k  -> workers (ws ++ [w]) [] k
        workers :: (Alg Err <: h, Alg Out <: h) => [Worker h] -> [Worker h] -> Hefty (Thread :+: h) a -> Hefty h a
        workers [] ws' m = main m ws'
        workers (Worker w : ws) ws' m = do
            s <- runThread w
            case s of
                Yielded k   -> workers ws (ws' ++ [Worker k]) m
                Forked w' k -> workers (ws ++ [w']) (ws' ++ [Worker k]) m
                _           -> workers ws ws' m

-- all executions through non-determinism
choose :: Alg NonDet <: h => Hefty h a -> Hefty h a -> Hefty h a
choose a b = do
    c <- liftNonDet choice
    if c then a else b

perms :: Alg NonDet <: h => [a] -> Hefty h [a]
perms ms = foldr (choose . return) (liftNonDet empty) $ permutations ms

executeAll :: (Alg Err <: h, Alg NonDet <: h, Alg Out <: h) => Hefty (Thread :+: h) a -> Hefty h a
executeAll t = main t []
    where
        main :: (Alg Err <: h, Alg NonDet <: h, Alg Out <: h) => Hefty (Thread :+: h) a -> [Worker h] -> Hefty h a
        main m ws = do
            s <- runThread m
            case s of
                Active a    -> if null ws then return a else liftNonDet empty
                Yielded k   -> do
                    if null ws then
                        main k ws
                    else do
                        p <- perms ws
                        choose (main k p) (workers p k)
                Forked w k  -> perms (w : ws) >>= \p -> choose (main k p) (workers p k)
        workers :: (Alg Err <: h, Alg NonDet <: h, Alg Out <: h) => [Worker h] -> Hefty (Thread :+: h) a -> Hefty h a
        workers [] m = main m []
        workers (Worker w : ws) m = do
            s <- runThread w
            case s of
                Active _    -> do
                    if null ws then
                        main m ws
                    else do
                        p <- perms ws
                        choose (main m p) (workers p m)
                Yielded k   -> perms (Worker k : ws) >>= \p -> choose (main m p) (workers p m)
                Forked w' k -> perms (w' : Worker k : ws) >>= \p -> choose (main m p) (workers p m)