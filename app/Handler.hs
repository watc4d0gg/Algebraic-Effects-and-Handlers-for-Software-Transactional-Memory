module Handler where

import Free

data Handler f a f' b = Handler { ret :: a -> Free f' b, hdlr :: f (Free f' b) -> Free f' b }

handle :: (Functor f, Functor f') => Handler f a f' b -> Free (f + f') a -> Free f' b
handle h = fold
    (ret h)
    (\case
        L x -> hdlr h x
        R x -> Op x)

hErr :: Functor f => Handler Err a f (Either String a)
hErr = Handler { ret = pure . Right, hdlr = \(Err s) -> pure (Left s) }

handleError :: Functor f => Free (Err + f) a -> Free f (Either String a)
handleError = handle hErr

data StatefulHandler f a s f' b = StatefulHandler { retS :: a -> (s -> Free f' b), hdlrS :: f (s -> Free f' b) -> (s -> Free f' b) }

handleStateful :: (Functor f, Functor f') => StatefulHandler f a s f' b -> s -> Free (f + f') a -> Free f' b
handleStateful h = flip $ fold
    (retS h)
    (\case
        L x -> hdlrS h x
        R x -> \s -> Op $ ($ s) <$> x)