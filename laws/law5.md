# $\verb!orElse!\ M\ \verb!retry!\leftrightarrow M$

```haskell
maybe (f Nothing) (f . Just) m = f m

> m = Nothing
    maybe (f Nothing) (f . Just) Nothing
=
    f Nothing


> m = Just x
    maybe (f Nothing) (f . Just) (Just x)
=
    (f . Just) x
=
    f (Just x)
```

For an arbitrary heap $h$ of size $n$:

```haskell
    handleSTM (orElse M retry) h
=
    handleStateful stmHandler (orElse M retry) h
=   
    fold
        (retS stmHandler)
        (\case
            L x -> hdlrS stmHandler x
            R x -> \s -> Op $ ($ s) <$> x)
        (Op $ L $ OrElse M retry)
        h
= 
    (\case
        L x -> hdlrS stmHandler x
        R x -> \s -> Op $ ($ s) <$> x)
        (fmap
            (fold
                (retS stmHandler)
                (\case
                    L x -> hdlrS stmHandler x
                    R x -> \s -> Op $ ($ s) <$> x))
            (L $ OrElse M retry))
        h
=
    (\case
        L x -> hdlrS stmHandler x
        R x -> \s -> Op $ ($ s) <$> x)
        (L $ OrElse
            (fold
                (retS stmHandler)
                (\case
                    L x -> hdlrS stmHandler x
                    R x -> \s -> Op $ ($ s) <$> x)
                M)
            (fold
                (retS stmHandler)
                (\case
                    L x -> hdlrS stmHandler x
                    R x -> \s -> Op $ ($ s) <$> x)
                retry))
        h
=
    hdlrS stmHandler
        (OrElse
            (fold
                (retS stmHandler)
                (\case
                    L x -> hdlrS stmHandler x
                    R x -> \s -> Op $ ($ s) <$> x)
                M)
            (fold
                (retS stmHandler)
                (\case
                    L x -> hdlrS stmHandler x
                    R x -> \s -> Op $ ($ s) <$> x)
                retry))
        h
=
    (\op h -> case op of
        New a k -> let (t, h') = alloc a h in k t h'
        Read t k -> let a = lookup t h in k a h
        Write t a k -> k $ update t a h
        Retry -> return Nothing
        OrElse t1 t2 -> t1 h >>= maybe (t2 h) (return . Just))
        (OrElse
            (fold
                (retS stmHandler)
                (\case
                    L x -> hdlrS stmHandler x
                    R x -> \s -> Op $ ($ s) <$> x)
                M)
            (fold
                (retS stmHandler)
                (\case
                    L x -> hdlrS stmHandler x
                    R x -> \s -> Op $ ($ s) <$> x)
                retry))
        h
=
    (>>=)
        (fold
            (retS stmHandler)
            (\case
                L x -> hdlrS stmHandler x
                R x -> \s -> Op $ ($ s) <$> x)
            M)
            h
        (maybe
            (fold
                (retS stmHandler)
                (\case
                    L x -> hdlrS stmHandler x
                    R x -> \s -> Op $ ($ s) <$> x)
                (Op $ L $ Retry))
                h
            (return . Just))
=
    (>>=)
        (fold
            (retS stmHandler)
            (\case
                L x -> hdlrS stmHandler x
                R x -> \s -> Op $ ($ s) <$> x)
            M)
            h
        (maybe
            (\case
                L x -> hdlrS stmHandler x
                R x -> \s -> Op $ ($ s) <$> x)
                (L $ Retry)
                h
            (return . Just))
=
    (>>=)
        (fold
            (retS stmHandler)
            (\case
                L x -> hdlrS stmHandler x
                R x -> \s -> Op $ ($ s) <$> x)
            M)
            h
        (maybe
            (\op h -> case op of
                New a k -> let (t, h') = alloc a h in k t h'
                Read t k -> let a = lookup t h in k a h
                Write t a k -> k $ update t a h
                Retry -> return Nothing
                OrElse t1 t2 -> t1 h >>= maybe (t2 h) (return . Just))
                Retry
                h
            (return . Just))
=
    (>>=)
        (fold
            (retS stmHandler)
            (\case
                L x -> hdlrS stmHandler x
                R x -> \s -> Op $ ($ s) <$> x)
            M)
            h
        (maybe
            (return Nothing)
            (return . Just))
=
    (>>=)
        (fold
            (retS stmHandler)
            (\case
                L x -> hdlrS stmHandler x
                R x -> \s -> Op $ ($ s) <$> x)
            M)
            h
        return
=   {using the monad law of right identity}
    fold
        (retS stmHandler)
        (\case
            L x -> hdlrS stmHandler x
            R x -> \s -> Op $ ($ s) <$> x)
        M
        h
=
    handleStateful stmHandler M h
=
    handleSTM M h
```