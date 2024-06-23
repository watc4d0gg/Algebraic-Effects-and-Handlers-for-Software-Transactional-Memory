# $(\verb!readTVar!\ a\ \verb!>>=!_{\text{STM}}\ \lambda x . \verb!writeTVar!\ a\ x)\leftrightarrow\verb!return!_{\text{STM}}()$

### Preliminaries

**Lemma 1**: We consider a heap $h$ with size $n$ (denoted $|h|$) to be a list of cells $c_{i}$ for $i \in [0, n)$, each holding a value $v_{i}$.

$$
    \verb!h = [Cell v!_{0}\verb!, Cell v!_{1}\ \dots\ \verb!Cell v!_{n - 1}\verb!]!
$$

For an arbitrary heap $h$ of size $n>0$ and for all transactional variables $t_{i}$ where $i \in [0, n)$, such that $t_{i}$ is properly initialized in $h$ $-$ through $\verb!newTVar!$, so that the value $v_{i}$ has the type referenced by $t_{i}$, it holds that
$$
    \verb!update (TVar i) (lookup (TVar i) h) h = h!
$$
Proof:
- $i = 0\ (n > 0,\ \text{thus}\ |h'| \geq 0)$:
    ```haskell
        update (TVar 0) (lookup (TVar 0) (Cell a : h')) (Cell a : h')
    =
        Cell (lookup (TVar 0) (Cell a : h')) : h'
    =
        Cell (unsafeCoerce a) : h'
    =   -- since t was properly initialized, unsafeCoerce coerces to the same type as v0
        Cell a : h'
    ```
- $i = k + 1\ (k \geq 0\ \text{and}\ n > k + 1)$
    ```haskell
        update (TVar (k + 1)) (lookup (TVar (k + 1)) (Cell v0 : h')) (Cell a : h')
    =   -- definition of update
        Cell a : update (TVar k) (lookup (TVar (k + 1)) (Cell a : h')) h'
    =   -- definition of lookup
        Cell a : update (TVar k) (lookup (TVar k) h') h'
    =   -- using induction hypothesis for i = k
        Cell a : h'

### Proof
For an arbitrary heap $h$ of size $n > 0$ and for all transactional variables $t_{i}$ which are properly initialized where $i \in [0, n)$:

```haskell
    handleSTM (Op $ L $ Read t (\a -> writeTVar t a)) h
=
    handleStateful hSTM (Op $ L $ Read t (\a -> writeTVar t a)) h
=   
    fold
        (retS hSTM)
        (\case
            L x -> hdlrS hSTM x
            R x -> \s -> Op $ ($ s) <$> x)
        (Op $ L $ Read t (\a -> writeTVar t a))
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
            (L $ Read t (\a -> writeTVar t a)))
        h
=
    (\case
        L x -> hdlrS hSTM x
        R x -> \s -> Op $ ($ s) <$> x)
        (L $ Read t (\a -> 
            (fold
                (retS hSTM)
                (\case
                    L x -> hdlrS hSTM x
                    R x -> \s -> Op $ ($ s) <$> x)
                writeTVar t a)))
        h
=
    hdlrS hSTM
        (Read t (\a -> 
            (fold
                (retS hSTM)
                (\case
                    L x -> hdlrS hSTM x
                    R x -> \s -> Op $ ($ s) <$> x)
                writeTVar t a)))
        h
=
    (\op h -> case op of
        New a k -> let (t, h') = alloc a h in k t h'
        Read t k -> let a = lookup t h in k a h
        Write t a k -> k $ update t a h
        Retry -> return Nothing
        OrElse t1 t2 -> t1 h >>= maybe (t2 h) (return . Just))
        (Read t (\a -> 
            (fold
                (retS hSTM)
                (\case
                    L x -> hdlrS hSTM x
                    R x -> \s -> Op $ ($ s) <$> x)
                writeTVar t a)))
        h
=
    let a = lookup t h
    in (\a ->
            (fold
                (retS hSTM)
                (\case
                    L x -> hdlrS hSTM x
                    R x -> \s -> Op $ ($ s) <$> x)
                writeTVar t a))
            a
            h
=
    (\a ->
        (fold
            (retS hSTM)
            (\case
                L x -> hdlrS hSTM x
                R x -> \s -> Op $ ($ s) <$> x)
            writeTVar t a))
        (lookup t h)
        h
=
    (fold
        (retS hSTM)
        (\case
            L x -> hdlrS hSTM x
            R x -> \s -> Op $ ($ s) <$> x)
        writeTVar t (lookup t h)))
        h
=
    (fold
        (retS hSTM)
        (\case
            L x -> hdlrS hSTM x
            R x -> \s -> Op $ ($ s) <$> x)
        (Op $ L $ Write t (lookup t h) (Pure ())))
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
            (L $ Write t (lookup t h) (Pure ())))
        h
=
    (\case
        L x -> hdlrS hSTM x
        R x -> \s -> Op $ ($ s) <$> x)
        (L $ Write t (lookup t h)
            (fold
                (retS hSTM)
                (\case
                    L x -> hdlrS hSTM x
                    R x -> \s -> Op $ ($ s) <$> x)
                (Pure ()))
        h
=
    hdlrS hSTM
        (Write t (lookup t h)
            (fold
                (retS hSTM)
                (\case
                    L x -> hdlrS hSTM x
                    R x -> \s -> Op $ ($ s) <$> x)
                (Pure ())))
        h
=
    (\op h -> case op of
        New a k -> let (t, h') = alloc a h in k t h'
        Read t k -> let a = lookup t h in k a h
        Write t a k -> k $ update t a h
        Retry -> return Nothing
        OrElse t1 t2 -> t1 h >>= maybe (t2 h) (return . Just))
        (Write t (lookup t h)
            (fold
                (retS hSTM)
                (\case
                    L x -> hdlrS hSTM x
                    R x -> \s -> Op $ ($ s) <$> x)
                (Pure ())))
        h
=
    (fold
        (retS hSTM)
        (\case
            L x -> hdlrS hSTM x
            R x -> \s -> Op $ ($ s) <$> x)
        (Pure ()))
        (update t (lookup t h) h)
=   -- using Lemma 1
    (fold
        (retS hSTM)
        (\case
            L x -> hdlrS hSTM x
            R x -> \s -> Op $ ($ s) <$> x)
        (Pure ()))
        h
=
    handleStateful hSTM (Pure ()) h
=
    handleSTM (Pure ()) h
=
    handleSTM (return ()) h
```