# $\verb!orElse!\ \verb!retry!\ M\leftrightarrow M$

For an arbitrary heap $h$ of size $n$:

```haskell
    handleSTM (orElse retry M) h
=
    handleStateful stmHandler (orElse retry M) h
=   
    fold
        (retS stmHandler)
        (\case
            L x -> hdlrS stmHandler x
            R x -> \s -> Op $ ($ s) <$> x)
        (Op $ L $ OrElse retry M)
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
            (L $ OrElse retry M))
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
                retry)
            (fold
                (retS stmHandler)
                (\case
                    L x -> hdlrS stmHandler x
                    R x -> \s -> Op $ ($ s) <$> x)
                M))
        h
=
    hdlrS stmHandler
        (OrElse
            (fold
                (retS stmHandler)
                (\case
                    L x -> hdlrS stmHandler x
                    R x -> \s -> Op $ ($ s) <$> x)
                retry)
            (fold
                (retS stmHandler)
                (\case
                    L x -> hdlrS stmHandler x
                    R x -> \s -> Op $ ($ s) <$> x)
                M))
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
                retry)
            (fold
                (retS stmHandler)
                (\case
                    L x -> hdlrS stmHandler x
                    R x -> \s -> Op $ ($ s) <$> x)
                M))
        h
=
    (>>=)
        (fold
            (retS stmHandler)
            (\case
                L x -> hdlrS stmHandler x
                R x -> \s -> Op $ ($ s) <$> x)
            (Op $ L $ Retry))
            h
        (maybe
            (fold
                (retS stmHandler)
                (\case
                    L x -> hdlrS stmHandler x
                    R x -> \s -> Op $ ($ s) <$> x)
                M)
                h
            (return . Just))
=
    (>>=)
        (\case
            L x -> hdlrS stmHandler x
            R x -> \s -> Op $ ($ s) <$> x)
            (L $ Retry)
            h
        (maybe
            (fold
                (retS stmHandler)
                (\case
                    L x -> hdlrS stmHandler x
                    R x -> \s -> Op $ ($ s) <$> x)
                M)
                h
            (return . Just))
=
    (>>=)
        (\op h -> case op of
            New a k -> let (t, h') = alloc a h in k t h'
            Read t k -> let a = lookup t h in k a h
            Write t a k -> k $ update t a h
            Retry -> return Nothing
            OrElse t1 t2 -> t1 h >>= maybe (t2 h) (return . Just))
            Retry
            h
        (maybe
            (fold
                (retS stmHandler)
                (\case
                    L x -> hdlrS stmHandler x
                    R x -> \s -> Op $ ($ s) <$> x)
                M)
                h
            (return . Just))
=
    (>>=)
        (Pure Nothing)
        (maybe
            (fold
                (retS stmHandler)
                (\case
                    L x -> hdlrS stmHandler x
                    R x -> \s -> Op $ ($ s) <$> x)
                M)
                h
            (return . Just))
=
    fold 
        (maybe
            (fold
                (retS stmHandler)
                (\case
                    L x -> hdlrS stmHandler x
                    R x -> \s -> Op $ ($ s) <$> x)
                M)
                h
            (return . Just))
        Op
        (Pure Nothing)
=
    (maybe
        (fold
            (retS stmHandler)
            (\case
                L x -> hdlrS stmHandler x
                R x -> \s -> Op $ ($ s) <$> x)
            M)
            h
        (return . Just))
    Nothing
=
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