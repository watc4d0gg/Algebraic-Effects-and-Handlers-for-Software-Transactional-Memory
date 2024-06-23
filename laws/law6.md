# $\verb!orElse!\ M_{1}\ (\verb!orElse!\ M_{2}\ M_{3})\leftrightarrow \verb!orElse!\ (\verb!orElse!\ M_{1}\ M_{2})\ M_{3}$

For an arbitrary heap $h$ of size $n$:

```haskell
    handleSTM (orElse (orElse M_1 M_2) M_3) h
=
    handleStateful stmHandler (orElse (orElse M_1 M_2) M_3) h
=   
    fold
        (retS stmHandler)
        (\case
            L x -> hdlrS stmHandler x
            R x -> \s -> Op $ ($ s) <$> x)
        (Op $ L $ OrElse (orElse M_1 M_2) M_3)
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
            (L $ OrElse (orElse M_1 M_2) M_3)
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
                (orElse M_1 M_2))
            (fold
                (retS stmHandler)
                (\case
                    L x -> hdlrS stmHandler x
                    R x -> \s -> Op $ ($ s) <$> x)
                M_3))
        h
=
    hdlrS stmHandler
        (OrElse
            (fold
                (retS stmHandler)
                (\case
                    L x -> hdlrS stmHandler x
                    R x -> \s -> Op $ ($ s) <$> x)
                (orElse M_1 M_2))
            (fold
                (retS stmHandler)
                (\case
                    L x -> hdlrS stmHandler x
                    R x -> \s -> Op $ ($ s) <$> x)
                M_3))
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
                (orElse M_1 M_2))
            (fold
                (retS stmHandler)
                (\case
                    L x -> hdlrS stmHandler x
                    R x -> \s -> Op $ ($ s) <$> x)
                M_3))
        h
=
    (>>=)
        (fold
            (retS stmHandler)
            (\case
                L x -> hdlrS stmHandler x
                R x -> \s -> Op $ ($ s) <$> x)
            (Op $ L $ OrElse M_1 M_2)
            h)
        (maybe
            (fold
                (retS stmHandler)
                (\case
                    L x -> hdlrS stmHandler x
                    R x -> \s -> Op $ ($ s) <$> x)
                M_3
                h)
            (return . Just))
=
    (>>=)
        ((\case
            L x -> hdlrS stmHandler x
            R x -> \s -> Op $ ($ s) <$> x)
            (L $ OrElse
                (fold
                    (retS stmHandler)
                    (\case
                        L x -> hdlrS stmHandler x
                        R x -> \s -> Op $ ($ s) <$> x)
                    M_1)
                (fold
                    (retS stmHandler)
                    (\case
                        L x -> hdlrS stmHandler x
                        R x -> \s -> Op $ ($ s) <$> x)
                    M_2))
            h)
        (maybe
            (fold
                (retS stmHandler)
                (\case
                    L x -> hdlrS stmHandler x
                    R x -> \s -> Op $ ($ s) <$> x)
                M_3
                h)
            (return . Just))
=
    (>>=)
        (hdlrS stmHandler
            (OrElse
                (fold
                    (retS stmHandler)
                    (\case
                        L x -> hdlrS stmHandler x
                        R x -> \s -> Op $ ($ s) <$> x)
                    M_1)
                (fold
                    (retS stmHandler)
                    (\case
                        L x -> hdlrS stmHandler x
                        R x -> \s -> Op $ ($ s) <$> x)
                    M_2))
            h)
        (maybe
            (fold
                (retS stmHandler)
                (\case
                    L x -> hdlrS stmHandler x
                    R x -> \s -> Op $ ($ s) <$> x)
                M_3
                h)
            (return . Just))
=
    (>>=)
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
                    M_1)
                (fold
                    (retS stmHandler)
                    (\case
                        L x -> hdlrS stmHandler x
                        R x -> \s -> Op $ ($ s) <$> x)
                    M_2))
            h)
        (maybe
            (fold
                (retS stmHandler)
                (\case
                    L x -> hdlrS stmHandler x
                    R x -> \s -> Op $ ($ s) <$> x)
                M_3
                h)
            (return . Just))
=
    (>>=)
        ((>>=)
            (fold
                (retS stmHandler)
                (\case
                    L x -> hdlrS stmHandler x
                    R x -> \s -> Op $ ($ s) <$> x)
                M_1
                h)
            (maybe
                (fold
                    (retS stmHandler)
                    (\case
                        L x -> hdlrS stmHandler x
                        R x -> \s -> Op $ ($ s) <$> x)
                    M_2
                    h)
                (return . Just)))
        (maybe
            (fold
                (retS stmHandler)
                (\case
                    L x -> hdlrS stmHandler x
                    R x -> \s -> Op $ ($ s) <$> x)
                M_3
                h)
            (return . Just))
=   {using the monad law of associativity}
    (>>=)
        (fold
            (retS stmHandler)
            (\case
                L x -> hdlrS stmHandler x
                R x -> \s -> Op $ ($ s) <$> x)
            M_1
            h)
        (\x ->
            (>>=)
                (maybe
                    (fold
                        (retS stmHandler)
                        (\case
                            L x -> hdlrS stmHandler x
                            R x -> \s -> Op $ ($ s) <$> x)
                        M_2
                        h)
                    (return . Just)
                    x)
                (maybe
                    (fold
                        (retS stmHandler)
                        (\case
                            L x -> hdlrS stmHandler x
                            R x -> \s -> Op $ ($ s) <$> x)
                        M_3
                        h)
                    (return . Just)))
=   {by cases on x}
    - x = Nothing
        (>>=)
            (maybe
                (fold
                    (retS stmHandler)
                    (\case
                        L x -> hdlrS stmHandler x
                        R x -> \s -> Op $ ($ s) <$> x)
                    M_2
                    h)
                (return . Just)
                Nothing)
            (maybe
                (fold
                    (retS stmHandler)
                    (\case
                        L x -> hdlrS stmHandler x
                        R x -> \s -> Op $ ($ s) <$> x)
                    M_3
                    h)
                (return . Just))
    =   {definition of maybe}
        (>>=)
            (fold
                (retS stmHandler)
                (\case
                    L x -> hdlrS stmHandler x
                    R x -> \s -> Op $ ($ s) <$> x)
                M_2
                h)
            (maybe
                (fold
                    (retS stmHandler)
                    (\case
                        L x -> hdlrS stmHandler x
                        R x -> \s -> Op $ ($ s) <$> x)
                    M_3
                    h)
                (return . Just))
    =
        maybe
            ((>>=)
                (fold
                    (retS stmHandler)
                    (\case
                        L x -> hdlrS stmHandler x
                        R x -> \s -> Op $ ($ s) <$> x)
                    M_2
                    h)
                (maybe
                    (fold
                        (retS stmHandler)
                        (\case
                            L x -> hdlrS stmHandler x
                            R x -> \s -> Op $ ($ s) <$> x)
                        M_3
                        h)
                    (return . Just)))
            (return . Just)
            Nothing

    - x = Just a
        (>>=)
            (maybe
                (fold
                    (retS stmHandler)
                    (\case
                        L x -> hdlrS stmHandler x
                        R x -> \s -> Op $ ($ s) <$> x)
                    M_2
                    h)
                (return . Just)
                (Just a))
            (maybe
                (fold
                    (retS stmHandler)
                    (\case
                        L x -> hdlrS stmHandler x
                        R x -> \s -> Op $ ($ s) <$> x)
                    M_3
                    h)
                (return . Just))
    =
        (>>=)
            (return (Just a))
            (maybe
                (fold
                    (retS stmHandler)
                    (\case
                        L x -> hdlrS stmHandler x
                        R x -> \s -> Op $ ($ s) <$> x)
                    M_3
                    h)
                (return . Just))
    =   {using the monad law of left identity}
        maybe
            (fold
                (retS stmHandler)
                (\case
                    L x -> hdlrS stmHandler x
                    R x -> \s -> Op $ ($ s) <$> x)
                M_3
                h)
            (return . Just)
            (Just a)
    =   {definition of maybe}
        return (Just a)
    =
        maybe
            ((>>=)
                (fold
                    (retS stmHandler)
                    (\case
                        L x -> hdlrS stmHandler x
                        R x -> \s -> Op $ ($ s) <$> x)
                    M_2
                    h)
                (maybe
                    (fold
                        (retS stmHandler)
                        (\case
                            L x -> hdlrS stmHandler x
                            R x -> \s -> Op $ ($ s) <$> x)
                        M_3
                        h)
                    (return . Just)))
            (return . Just)
            (Just a)
=
    (>>=)
        (fold
            (retS stmHandler)
            (\case
                L x -> hdlrS stmHandler x
                R x -> \s -> Op $ ($ s) <$> x)
            M_1
            h)
        (maybe
            ((>>=)
                (fold
                    (retS stmHandler)
                    (\case
                        L x -> hdlrS stmHandler x
                        R x -> \s -> Op $ ($ s) <$> x)
                    M_2
                    h)
                (maybe
                    (fold
                        (retS stmHandler)
                        (\case
                            L x -> hdlrS stmHandler x
                            R x -> \s -> Op $ ($ s) <$> x)
                        M_3
                        h)
                    (return . Just)))
            (return . Just))
=
    (>>=)
        (fold
            (retS stmHandler)
            (\case
                L x -> hdlrS stmHandler x
                R x -> \s -> Op $ ($ s) <$> x)
            M_1
            h)
        (maybe
            ((\op h -> case op of
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
                        M_2)
                    (fold
                        (retS stmHandler)
                        (\case
                            L x -> hdlrS stmHandler x
                            R x -> \s -> Op $ ($ s) <$> x)
                        M_3))
                h)
            (return . Just))
=
    (>>=)
        (fold
            (retS stmHandler)
            (\case
                L x -> hdlrS stmHandler x
                R x -> \s -> Op $ ($ s) <$> x)
            M_1
            h)
        (maybe
            (hdlrS stmHandler
                (OrElse
                    (fold
                        (retS stmHandler)
                        (\case
                            L x -> hdlrS stmHandler x
                            R x -> \s -> Op $ ($ s) <$> x)
                        M_2)
                    (fold
                        (retS stmHandler)
                        (\case
                            L x -> hdlrS stmHandler x
                            R x -> \s -> Op $ ($ s) <$> x)
                        M_3))
                h)
            (return . Just))
=
    (>>=)
        (fold
            (retS stmHandler)
            (\case
                L x -> hdlrS stmHandler x
                R x -> \s -> Op $ ($ s) <$> x)
            M_1
            h)
        (maybe
            ((\case
                L x -> hdlrS stmHandler x
                R x -> \s -> Op $ ($ s) <$> x)
                (L $ OrElse
                    (fold
                        (retS stmHandler)
                        (\case
                            L x -> hdlrS stmHandler x
                            R x -> \s -> Op $ ($ s) <$> x)
                        M_2))
                h)
            (return . Just))
=
    (>>=)
        (fold
            (retS stmHandler)
            (\case
                L x -> hdlrS stmHandler x
                R x -> \s -> Op $ ($ s) <$> x)
            M_1
            h)
        (maybe
            ((\case
                L x -> hdlrS stmHandler x
                R x -> \s -> Op $ ($ s) <$> x)
                (fmap
                    (fold
                        (retS stmHandler)
                        (\case
                            L x -> hdlrS stmHandler x
                            R x -> \s -> Op $ ($ s) <$> x))
                    (L $ OrElse M_2 M_3))
                h)
            (return . Just))
=
    (>>=)
        (fold
            (retS stmHandler)
            (\case
                L x -> hdlrS stmHandler x
                R x -> \s -> Op $ ($ s) <$> x)
            M_1
            h)
        (maybe
            (fold
                (retS stmHandler)
                (\case
                    L x -> hdlrS stmHandler x
                    R x -> \s -> Op $ ($ s) <$> x)
                (Op $ L $ OrElse M_2 M_3)
                h)
            (return . Just))
=
    (>>=)
        (fold
            (retS stmHandler)
            (\case
                L x -> hdlrS stmHandler x
                R x -> \s -> Op $ ($ s) <$> x)
            M_1
            h)
        (maybe
            (fold
                (retS stmHandler)
                (\case
                    L x -> hdlrS stmHandler x
                    R x -> \s -> Op $ ($ s) <$> x)
                (orElse M_2 M_3)
                h)
            (return . Just))
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
                M_1)
            (fold
                (retS stmHandler)
                (\case
                    L x -> hdlrS stmHandler x
                    R x -> \s -> Op $ ($ s) <$> x)
                (orElse M_2 M_3)))
        h
=
    hdlrS stmHandler
        (OrElse
            (fold
                (retS stmHandler)
                (\case
                    L x -> hdlrS stmHandler x
                    R x -> \s -> Op $ ($ s) <$> x)
                M_1)
            (fold
                (retS stmHandler)
                (\case
                    L x -> hdlrS stmHandler x
                    R x -> \s -> Op $ ($ s) <$> x)
                (orElse M_2 M_3)))
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
                M_1)
            (fold
                (retS stmHandler)
                (\case
                    L x -> hdlrS stmHandler x
                    R x -> \s -> Op $ ($ s) <$> x)
                (orElse M_2 M_3)))
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
            (L $ OrElse M_1 (orElse M_2 M_3))
        h
=   
    fold
        (retS stmHandler)
        (\case
            L x -> hdlrS stmHandler x
            R x -> \s -> Op $ ($ s) <$> x)
        (Op $ L $ OrElse M_1 (orElse M_2 M_3))
        h
=
    handleStateful stmHandler (orElse M_1 (orElse M_2 M_3)) h
=
    handleSTM (orElse M_1 (orElse M_2 M_3)) h
```