module Free where

data Free f a where
    Pure :: a -> Free f a
    Op :: f (Free f a) -> Free f a

fold :: Functor f => (a -> b) -> (f b -> b) -> Free f a -> b
fold gen _   (Pure x) = gen x
fold gen alg (Op f)   = alg (fmap (fold gen alg) f)

instance Functor f => Monad (Free f) where
    (>>=) :: Functor f => Free f a -> (a -> Free f b) -> Free f b
    m >>= k = fold k Op m

instance Functor f => Functor (Free f) where
    fmap :: Functor f => (a -> b) -> Free f a -> Free f b
    fmap f = fold (pure . f) Op

instance Functor f => Applicative (Free f) where
    pure :: Functor f => a -> Free f a
    pure = Pure

    (<*>) :: Functor f => Free f (a -> b) -> Free f a -> Free f b
    f <*> m = fold (<$> m) Op f

-- functor coproduct
infixr 6 +
data (f + g) a = L (f a) | R (g a)
    deriving Functor

-- functor subtyping
class (Functor f, Functor g) => f < g where
    inj :: f k -> g k

instance {-# OVERLAPPING #-} Functor f => f < f where
    inj :: f k -> f k
    inj = id

instance {-# OVERLAPPING #-} (Functor f, Functor g) => f < (f + g) where
    inj :: f k -> (f + g) k
    inj = L

instance {-# OVERLAPPING #-} (Functor f, Functor g, Functor h, f < h) => f < (g + h) where
    inj :: f < h => f k -> (g + h) k
    inj = R . inj

-- -- natural transformation
-- type f ~> g = forall a. f a -> g a

-- -- functor isomorphism
-- data f <-> g = Iso { to :: f ~> g, from :: g ~> f }

-- (<->) :: (f ~> g) -> (g ~> f) -> (f <-> g)
-- (<->) = Iso

-- sum :: (f a -> b) -> (g a -> b) -> (f + g) a -> b
-- sum f _ (L x) = f x
-- sum _ g (R x) = g x

-- isoRefl :: f <-> f
-- isoRefl = id <-> id

-- isoSym :: (f <-> g) -> (g <-> f)
-- isoSym i = from i <-> to i

-- isoTrans :: (f <-> g) -> (g <-> h) -> (f <-> h)
-- isoTrans i1 i2 = (to i2 . to i1) <-> (from i1 . from i2)

-- isoSumCong :: (f <-> f') -> (g <-> g') -> ((f + g) <-> (f' + g'))
-- isoSumCong i1 i2 = sum (L . to i1) (R . to i2) <-> sum (L . from i1) (R . from i2)

-- isoSumComm :: (f + g) <-> (g + f)
-- isoSumComm = sum R L <-> sum R L

-- isoSumAssoc :: (f + (g + h)) <-> ((f + g) + h)
-- isoSumAssoc = sum (L . L) (sum (L . R) R) <-> sum (sum L (R . L)) (R . R)

-- data Forephism f g = forall f'. (Functor g, Functor f, Functor f') => Forephism { iso :: g <-> (f + f') }

-- class (Functor f, Functor g) => f < g where
--     forephism :: Forephism f g

-- inj :: f < g => f a -> g a
-- inj = case forephism of
--     Forephism i -> from i . L

-- instance {-# OVERLAPPING #-} Functor f => f < f where 
--     forephism :: Forephism f f
--     forephism = Forephism (L <-> sum id (\(x :: End a) -> case x of))

-- instance {-# OVERLAPPING #-} (Functor f, Functor g) => f < (f + g) where 
--     forephism :: f < (f + g) => Forephism f (f + g)
--     forephism = Forephism isoRefl

-- instance {-# OVERLAPPING #-} (Functor f, Functor g, Functor h, f < h) => f < (g + h) where 
--     forephism :: (f < h) => Forephism f (g + h)
--     forephism = case forephism of
--         Forephism i -> Forephism (isoTrans (isoSumCong isoRefl i) (isoTrans isoSumComm (isoSym isoSumAssoc)))

data End k
    deriving Functor

un :: Free End a -> a
un (Pure x) = x
un (Op f) = case f of

newtype Err k = Err String
    deriving Functor

err :: Err < f => String -> Free f a
err str = Op $ inj $ Err str