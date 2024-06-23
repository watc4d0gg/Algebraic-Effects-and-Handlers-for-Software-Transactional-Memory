# $(\verb!readTVar!\ a\ \verb!>>=!_{\text{STM}}\ \lambda x . \verb!writeTVar!\ b\ M\ \verb!>>=!_{\text{STM}}\ \verb!return!_{\text{STM}}\ x)\leftrightarrow(\verb!writeTVar!\ b\ N\ \verb!>>!_{\text{STM}}\ \verb!readTVar!\ a)\ \text{if}\ a\neq b$

### Preliminaries

**Lemma 3**: For an arbitrary heap $h$ of size $n \geq 2$ and for all transactional variable $t_{i}$ and $t_{j}$ where $i, j \in [0, n)$ and $i \neq j$, with $t_{i}$ and $t_{j}$ being properly initialized in $h$, it holds that:
$$
    \verb!lookup (TVar i) (update (TVar j) x h) = lookup (TVar i) h!
$$
Proof:
- $i = 0$:
    ```haskell
        lookup (TVar 0) (update (TVar j) x (Cell a : h'))
    =
        lookup (TVar 0) (Cell a : update (TVar (j - 1)) x h')
    =
        unsafeCoerce a
    =
        lookup (TVar 0) (Cell a : h')
    ```
- $i = k + 1$:
    ```haskell
        lookup (TVar (k + 1)) (update (TVar j) x (Cell a : h'))
    ```
    - We consider these cases for $j$:
        - $j = 0$:
            ```haskell
                lookup (TVar (k + 1)) (update (TVar 0) x (Cell a : h'))
            =
                lookup (TVar (k + 1)) (Cell x : h')
            =
                lookup (TVar k) h'
            =
                lookup (TVar (k + 1)) (Cell a : h')
            ```
        - $j = l + 1$
            ```haskell
                lookup (TVar (k + 1)) (update (TVar (l + 1)) x (Cell a : h'))
            =
                lookup (TVar (k + 1)) (Cell a : update (TVar l) x h')
            =
                lookup (TVar k) (update (TVar l) x h')
            =   -- using induction hypothesis for i = k and j = l
                lookup (TVar k) h'
            =
                lookup (TVar (k + 1)) (Cell a : h')
            ```

### Proof
For an arbitrary heap $h$ of size $n \geq 2$ and for all transactional variables $t_{i}$ and $t_{j}$ where $i, j \in [0, n)$ and $i \neq j$, with $t_{i}$ and $t_{j}$ being properly initialized in $h$:

```haskell
    handleSTM (Op $ L $ Read t_i (\x -> Op $ L $ Write t_j b (Pure x))) h
=
    handleStateful hSTM (Op $ L $ Read t_i (\x -> Op $ L $ Write t_j b (Pure x))) h
=
    fold
        (retS hSTM)
        (\case
            L x -> hdlrS hSTM x
            R x -> \s -> Op $ ($ s) <$> x)
        (Op $ L $ Read t_i (\x -> Op $ L $ Write t_j b (Pure x)))
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
            (L $ Read t_i (\x -> Op $ L $ Write t_j b (Pure x)))
        h
=
    (\case
        L x -> hdlrS hSTM x
        R x -> \s -> Op $ ($ s) <$> x)
        (L $ Read t_i (\x ->
            (fold
                (retS hSTM)
                (\case
                    L x -> hdlrS hSTM x
                    R x -> \s -> Op $ ($ s) <$> x)
                (Op $ L $ Write t_j b (Pure x)))))
        h
=
    hdlrS hSTM
        (Read t_i (\x ->
            (fold
                (retS hSTM)
                (\case
                    L x -> hdlrS hSTM x
                    R x -> \s -> Op $ ($ s) <$> x)
                (Op $ L $ Write t_j b (Pure x)))))
        h
=
    (\op h -> case op of
        New a k -> let (t, h') = alloc a h in k t h'
        Read t k -> let a = lookup t h in k a h
        Write t a k -> k $ update t a h
        Retry -> return Nothing
        OrElse t1 t2 -> t1 h >>= maybe (t2 h) (return . Just))
        (Read t_i (\x ->
            (fold
                (retS hSTM)
                (\case
                    L x -> hdlrS hSTM x
                    R x -> \s -> Op $ ($ s) <$> x)
                (Op $ L $ Write t_j b (Pure x)))))
        h
=
    let a = lookup t_i h
    in (\x ->
            (fold
                (retS hSTM)
                (\case
                    L x -> hdlrS hSTM x
                    R x -> \s -> Op $ ($ s) <$> x)
                (Op $ L $ Write t_j b (Pure x))))
        a
        h
=
    (\x ->
        (fold
            (retS hSTM)
            (\case
                L x -> hdlrS hSTM x
                R x -> \s -> Op $ ($ s) <$> x)
            (Op $ L $ Write t_j b (Pure x))))
        (lookup t_i h)
        h
=
    (fold
        (retS hSTM)
        (\case
            L x -> hdlrS hSTM x
            R x -> \s -> Op $ ($ s) <$> x)
        (Op $ L $ Write t_j b (Pure (lookup t_i h))))
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
                    R x -> \s -> Op $ ($ s) <$> x)
            (L $ Write t_j b (Pure (lookup t_i h)))))
        h
=
    (\case
        L x -> hdlrS hSTM x
        R x -> \s -> Op $ ($ s) <$> x)
        (L $ Write t_j b
            (fold
                (retS hSTM)
                (\case
                    L x -> hdlrS hSTM x
                    R x -> \s -> Op $ ($ s) <$> x)
                (Pure (lookup t_i h))))
        h
=
    hdlrS hSTM
        (Write t_j b
            (fold
                (retS hSTM)
                (\case
                    L x -> hdlrS hSTM x
                    R x -> \s -> Op $ ($ s) <$> x)
                (Pure (lookup t_i h))))
        h
=
    (\op h -> case op of
        New a k -> let (t, h') = alloc a h in k t h'
        Read t k -> let a = lookup t h in k a h
        Write t a k -> k $ update t a h
        Retry -> return Nothing
        OrElse t1 t2 -> t1 h >>= maybe (t2 h) (return . Just))
        (Write t_j b
            (fold
                (retS hSTM)
                (\case
                    L x -> hdlrS hSTM x
                    R x -> \s -> Op $ ($ s) <$> x)
                (Pure (lookup t_i h))))
        h
=
    (fold
        (retS hSTM)
        (\case
            L x -> hdlrS hSTM x
            R x -> \s -> Op $ ($ s) <$> x)
        (Pure (lookup t_i h)))
        (update t_j b h)
=   -- using Lemma 3
    (fold
        (retS hSTM)
        (\case
            L x -> hdlrS hSTM x
            R x -> \s -> Op $ ($ s) <$> x)
        (Pure (lookup t_i (update t_j b h))))
        (update t_j b h)
=
    (\a ->
        (fold
            (retS hSTM)
            (\case
                L x -> hdlrS hSTM x
                R x -> \s -> Op $ ($ s) <$> x)
            (Pure a)))
        (lookup t_i (update t_j b h))
        (update t_j b h)
=
    let a = lookup t_i (update t_j b h)
    in (\x -> 
            (fold
                (retS hSTM)
                (\case
                    L x -> hdlrS hSTM x
                    R x -> \s -> Op $ ($ s) <$> x)
                (Pure x)))
        a
        (update t_j b h)
=
    (\op h -> case op of
        New a k -> let (t, h') = alloc a h in k t h'
        Read t k -> let a = lookup t h in k a h
        Write t a k -> k $ update t a h
        Retry -> return Nothing
        OrElse t1 t2 -> t1 h >>= maybe (t2 h) (return . Just))
        (Read t_i (\x ->
            (fold
                (retS hSTM)
                (\case
                    L x -> hdlrS hSTM x
                    R x -> \s -> Op $ ($ s) <$> x)
                (Pure x))))
        (update t_j b h)
=
    hdlrS hSTM
        (Read t_i (\x ->
            (fold
                (retS hSTM)
                (\case
                    L x -> hdlrS hSTM x
                    R x -> \s -> Op $ ($ s) <$> x)
                (Pure x))))
        (update t_j b h)
=
    (\case
        L x -> hdlrS hSTM x
        R x -> \s -> Op $ ($ s) <$> x)
        (L $ Read t_i (\x ->
            (fold
                (retS hSTM)
                (\case
                    L x -> hdlrS hSTM x
                    R x -> \s -> Op $ ($ s) <$> x)
                (Pure x))))
        (update t_j b h)
=
    (\case
        L x -> hdlrS hSTM x
        R x -> \s -> Op $ ($ s) <$> x)
        (fmap
            (fold
                (retS hSTM)
                (\case
                    L x -> hdlrS hSTM x
                    R x -> \s -> Op $ ($ s) <$> x)
            (L $ Read t_i Pure)))
        h
=
    (fold
        (retS hSTM)
        (\case
            L x -> hdlrS hSTM x
            R x -> \s -> Op $ ($ s) <$> x)
        (Op $ L $ Read t_i Pure))
        (update t_j b h)
=
    (fold
        (retS hSTM)
        (\case
            L x -> hdlrS hSTM x
            R x -> \s -> Op $ ($ s) <$> x)
        readTVar t_i)
        (update t_j b h)
=
    (\op h -> case op of
        New a k -> let (t, h') = alloc a h in k t h'
        Read t k -> let a = lookup t h in k a h
        Write t a k -> k $ update t a h
        Retry -> return Nothing
        OrElse t1 t2 -> t1 h >>= maybe (t2 h) (return . Just))
        (Write t_j b
            (fold
                (retS hSTM)
                (\case
                    L x -> hdlrS hSTM x
                    R x -> \s -> Op $ ($ s) <$> x)
                readTVar t_i))
        h
=
    hdlrS hSTM
        (Write t_j b
            (fold
                (retS hSTM)
                (\case
                    L x -> hdlrS hSTM x
                    R x -> \s -> Op $ ($ s) <$> x)
                readTVar t_i))
        h
=
    (\case
        L x -> hdlrS hSTM x
        R x -> \s -> Op $ ($ s) <$> x)
        (L $ Write t_j b
            (fold
                (retS hSTM)
                (\case
                    L x -> hdlrS hSTM x
                    R x -> \s -> Op $ ($ s) <$> x)
                readTVar t_i))
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
                    R x -> \s -> Op $ ($ s) <$> x)
            (L $ Write t_j b (readTVar t_i))))
        h
=
    (fold
        (retS hSTM)
        (\case
            L x -> hdlrS hSTM x
            R x -> \s -> Op $ ($ s) <$> x)
        (Op $ L $ Write t_j b (readTVar t_i)))
        h
=
    handleStateful hSTM (Op $ L $ Write t_j b (readTVar t_i)) h
=
    handleSTM (Op $ L $ Write t_j b (readTVar t_i)) h
```