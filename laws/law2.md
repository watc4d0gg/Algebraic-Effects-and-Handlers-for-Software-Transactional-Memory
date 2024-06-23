# $(\verb!writeTVar!\ a\ M\ \verb!>>!_{\text{STM}}\ \verb!writeTVar!\ b\ N)\leftrightarrow(\verb!writeTVar!\ b\ N\ \verb!>>!_{\text{STM}}\ \verb!writeTVar!\ a\ M)\ \text{if}\ a\neq b$

### Preliminaries

**Lemma 2**: For an arbitrary heap $h$ of size $n \geq 2$ and for all transactional variables $t_{i}$ and $t_{j}$ where $i, j \in [0, n)$ and $i \neq j$, with $t_{i}$ and $t_{j}$ being properly initialized in $h$, it holds that
$$
    \verb!update (TVar i) x (update (TVar j) y h) = update (TVar j) y (update (TVar i) x h)!
$$
Proof:
- $i = 0$:
    ```haskell
        update (TVar 0) x (update (TVar j) y (Cell a : h'))
    = -- since j != 0, update (TVar j) y (Cell a : h') = Cell a : update (TVar (j - 1)) y h'
        update (TVar 0) x (Cell a : update (TVar (j - 1) y h'))
    =
        Cell x : update (TVar (j - 1)) y h'
    =
        update (TVar j) y (Cell x : h')
    =
        update (TVar j) y (update (TVar 0) x (Cell a : h'))
    ```
- $i = k + 1$:
    ```haskell
        update (TVar (k + 1)) x (update (TVar j) y (Cell a : h'))
    ```
    - We consider these cases for $j$:
        - $j = 0$:
            ```haskell
                update (TVar (k + 1)) x (update (TVar 0) y (Cell a : h'))
            =
                update (TVar (k + 1)) x (Cell y : h')
            =
                Cell y : update (TVar k) x h'
            =
                update (TVar 0) y (Cell a : update (TVar k) x h')
            =
                update (TVar 0) y (update (TVar (k + 1)) x (Cell a : h'))
            ```
        - $j = l + 1$:
            ```haskell
                update (TVar (k + 1)) x (update (TVar (l + 1)) y (Cell a : h'))
            =
                update (TVar (k + 1)) x (Cell a : update (TVar l) y h')
            =
                Cell a : update (TVar k) x (update (TVar l) y h')
            =   -- using induction hypothesis for i = k and j = l
                Cell a : update (TVar l) y (update (TVar k) x h')
            =
                update (TVar (l + 1)) y (Cell a : update (TVar k) x h')
            =
                update (TVar (l + 1)) y (update (TVar (k + 1)) x (Cell a : h'))
            ```

### Proof
For an arbitrary heap $h$ of size $n \geq 2$ and for all transactional variables $t_{i}$ and $t_{j}$ where $i, j \in [0, n)$ and $i \neq j$, with $t_{i}$ and $t_{j}$ being properly initialized in $h$:

```haskell
    handleSTM (Op $ L $ Write t_i m (writeTVar t_j n)) h
=
    handleStateful hSTM (Op $ L $ Write t_i m (writeTVar t_j n)) h
=   
    fold
        (retS hSTM)
        (\case
            L x -> hdlrS hSTM x
            R x -> \s -> Op $ ($ s) <$> x)
        (Op $ L $ Write t_i m (writeTVar t_j n))
        h
= 
    (\case
        L x -> hdlrS hSTM x
        R x -> \s -> Op $ ($ s) <$> x)
        (fmap
            (fold
                (retS hSTM)
                (\case
                    L x -> hdlrS hSTM x
                    R x -> \s -> Op $ ($ s) <$> x))
            (L $ Write t_i m (writeTVar t_j n)))
        h
=
    (\case
        L x -> hdlrS hSTM x
        R x -> \s -> Op $ ($ s) <$> x)
        (L $ Write t_i m
            (fold
                (retS hSTM)
                (\case
                    L x -> hdlrS hSTM x
                    R x -> \s -> Op $ ($ s) <$> x)
                writeTVar t_j n))
        h
=
    hdlrS hSTM
        (Write t_i m
            (fold
                (retS hSTM)
                (\case
                    L x -> hdlrS hSTM x
                    R x -> \s -> Op $ ($ s) <$> x)
                writeTVar t_j n))
        h
=
    (\op h -> case op of
        New a k -> let (t, h') = alloc a h in k t h'
        Read t k -> let a = lookup t h in k a h
        Write t a k -> k $ update t a h
        Retry -> return Nothing
        OrElse t1 t2 -> t1 h >>= maybe (t2 h) (return . Just))
        (Write t_i m
            (fold
                (retS hSTM)
                (\case
                    L x -> hdlrS hSTM x
                    R x -> \s -> Op $ ($ s) <$> x)
                writeTVar t_j n))
        h
=
    (fold
        (retS hSTM)
        (\case
            L x -> hdlrS hSTM x
            R x -> \s -> Op $ ($ s) <$> x)
        writeTVar t_j n)
        (update t_i m h)
=
    (fold
        (retS hSTM)
        (\case
            L x -> hdlrS hSTM x
            R x -> \s -> Op $ ($ s) <$> x)
        (Op $ L $ Write t_j n (Pure ())))
        (update t_i m h)
=
    (\case
        L x -> hdlrS hSTM x
        R x -> \s -> Op $ ($ s) <$> x)
        (fmap
            (fold
                (retS hSTM)
                (\case
                    L x -> hdlrS hSTM x
                    R x -> \s -> Op $ ($ s) <$> x))
            (L $ Write t_j n (Pure ())))
        (update t_i m h)
=
    (\case
        L x -> hdlrS hSTM x
        R x -> \s -> Op $ ($ s) <$> x)
        (L $ Write t_j n
            (fold
                (retS hSTM)
                (\case
                    L x -> hdlrS hSTM x
                    R x -> \s -> Op $ ($ s) <$> x)
                (Pure ()))
        (update t_i m h)
=
    hdlrS hSTM
        (Write t_j n
            (fold
                (retS hSTM)
                (\case
                    L x -> hdlrS hSTM x
                    R x -> \s -> Op $ ($ s) <$> x)
                (Pure ())))
        (update t_i m h)
=
    (\op h -> case op of
        New a k -> let (t, h') = alloc a h in k t h'
        Read t k -> let a = lookup t h in k a h
        Write t a k -> k $ update t a h
        Retry -> return Nothing
        OrElse t1 t2 -> t1 h >>= maybe (t2 h) (return . Just))
        (Write t_j n
            (fold
                (retS hSTM)
                (\case
                    L x -> hdlrS hSTM x
                    R x -> \s -> Op $ ($ s) <$> x)
                (Pure ())))
        (update t_i m h)
=
    (fold
        (retS hSTM)
        (\case
            L x -> hdlrS hSTM x
            R x -> \s -> Op $ ($ s) <$> x)
        (Pure ()))
        (update t_j n (update t_i m h))
=   -- using Lemma 2
    (fold
        (retS hSTM)
        (\case
            L x -> hdlrS hSTM x
            R x -> \s -> Op $ ($ s) <$> x)
        (Pure ()))
        (update t_i m (update t_j n h))
=
    (\op h -> case op of
        New a k -> let (t, h') = alloc a h in k t h'
        Read t k -> let a = lookup t h in k a h
        Write t a k -> k $ update t a h
        Retry -> return Nothing
        OrElse t1 t2 -> t1 h >>= maybe (t2 h) (return . Just))
        (Write t_i m
            (fold
                (retS hSTM)
                (\case
                    L x -> hdlrS hSTM x
                    R x -> \s -> Op $ ($ s) <$> x)
                (Pure ())))
        (update t_j n h)
=
    hdlrS hSTM
        (Write t_i m
            (fold
                (retS hSTM)
                (\case
                    L x -> hdlrS hSTM x
                    R x -> \s -> Op $ ($ s) <$> x)
                (Pure ())))
        (update t_j n h)
=
    (\case
        L x -> hdlrS hSTM x
        R x -> \s -> Op $ ($ s) <$> x)
        (L $ Write t_i m
            (fold
                (retS hSTM)
                (\case
                    L x -> hdlrS hSTM x
                    R x -> \s -> Op $ ($ s) <$> x)
                (Pure ())))
        (update t_j n h)
=
    (\case
        L x -> hdlrS hSTM x
        R x -> \s -> Op $ ($ s) <$> x)
        (fmap
            (fold
                (retS hSTM)
                (\case
                    L x -> hdlrS hSTM x
                    R x -> \s -> Op $ ($ s) <$> x))
            (L $ Write t_i m (Pure ())))
        (update t_j n h)
=
    (fold
        (retS hSTM)
        (\case
            L x -> hdlrS hSTM x
            R x -> \s -> Op $ ($ s) <$> x)
        (Op $ L $ Write t_i m (Pure ())))
        (update t_j n h)
=
    (fold
        (retS hSTM)
        (\case
            L x -> hdlrS hSTM x
            R x -> \s -> Op $ ($ s) <$> x)
        writeTVar t_i m)
        (update t_j n h)
=
    (\op h -> case op of
        New a k -> let (t, h') = alloc a h in k t h'
        Read t k -> let a = lookup t h in k a h
        Write t a k -> k $ update t a h
        Retry -> return Nothing
        OrElse t1 t2 -> t1 h >>= maybe (t2 h) (return . Just))
        (Write t_j n
            (fold
                (retS hSTM)
                (\case
                    L x -> hdlrS hSTM x
                    R x -> \s -> Op $ ($ s) <$> x)
                writeTVar t_i m))
        h
=
    hdlrS hSTM
        (Write t_j n
            (fold
                (retS hSTM)
                (\case
                    L x -> hdlrS hSTM x
                    R x -> \s -> Op $ ($ s) <$> x)
                writeTVar t_i m))
        h
=
    (\case
        L x -> hdlrS hSTM x
        R x -> \s -> Op $ ($ s) <$> x)
        (L $ Write t_j n
            (fold
                (retS hSTM)
                (\case
                    L x -> hdlrS hSTM x
                    R x -> \s -> Op $ ($ s) <$> x)
                writeTVar t_i m))
        h
= 
    (\case
        L x -> hdlrS hSTM x
        R x -> \s -> Op $ ($ s) <$> x)
        (fmap
            (fold
                (retS hSTM)
                (\case
                    L x -> hdlrS hSTM x
                    R x -> \s -> Op $ ($ s) <$> x))
            (L $ Write t_j n (writeTVar t_i m)))
        h
=   
    fold
        (retS hSTM)
        (\case
            L x -> hdlrS hSTM x
            R x -> \s -> Op $ ($ s) <$> x)
        (Op $ L $ Write t_j n (writeTVar t_i m))
        h
=
    handleStateful hSTM (Op $ L $ Write t_j n (writeTVar t_i m)) h
=
    handleSTM (Op $ L $ Write t_j n (writeTVar t_i m)) h
```