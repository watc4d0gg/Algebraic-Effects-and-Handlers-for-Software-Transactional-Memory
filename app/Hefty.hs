module Hefty where
import Free hiding (type(+))
import Data.Kind (Type)

-- natural transformation
type f ~> g = forall a. f a -> g a

-- higher-order functor
class (forall x. Functor (h x)) => HFunctor h where
    hmap :: (f ~> g) -> (h f ~> h g)
    weave :: (Monad m, Monad n, Functor s) => s () -> (forall x. s (m x) -> n (s x)) -> (h m (m a) -> h n (n (s a)))

data Hefty h a where
    Return :: a -> Hefty h a
    Do :: h (Hefty h) (Hefty h a) -> Hefty h a

type Algebra h g = forall x. h g (g x) -> g x

hfold :: HFunctor h => (forall x. x -> g x) -> Algebra h g -> (Hefty h ~> g)
hfold gen _ (Return x) = gen x
hfold gen alg (Do h) = alg (fmap (hfold gen alg) (hmap (hfold gen alg) h))

ffold :: forall h g a b. HFunctor h => (forall x. x -> g x) -> Algebra h g -> (a -> b) -> (h g b -> b) -> Hefty h a -> b
ffold _ _ gen _ (Return x) = gen x
ffold hGen hAlg gen alg (Do h) = alg (hmap (hfold hGen hAlg) (fmap (ffold hGen hAlg gen alg) h))

instance HFunctor h => Monad (Hefty h) where
    (>>=) :: Hefty h a -> (a -> Hefty h b) -> Hefty h b
    m >>= k = ffold Return Do k Do m

instance HFunctor h => Functor (Hefty h) where
    fmap :: (a -> b) -> Hefty h a -> Hefty h b
    fmap f = ffold Return Do (pure . f) Do

instance HFunctor h => Applicative (Hefty h) where
    pure :: a -> Hefty h a
    pure = Return

    (<*>) :: Hefty h (a -> b) -> Hefty h a -> Hefty h b
    f <*> m = ffold Return Do (<$> m) Do f

-- higher-order functor coproducts
infixr 6 :+:
data (f :+: g) (m :: Type -> Type) a = HL (f m a) | HR (g m a)
    deriving Functor

instance (HFunctor f, HFunctor g) => HFunctor (f :+: g) where
    hmap :: (a ~> b) -> (f :+: g) a ~> (f :+: g) b
    hmap f (HL x) = HL (hmap f x)
    hmap f (HR x) = HR (hmap f x)

    weave :: (Monad m, Monad n, Functor s) => s () -> (forall x. s (m x) -> n (s x)) -> (f :+: g) m (m a) -> (f :+: g) n (n (s a))
    weave s t (HL x) = HL (weave s t x)
    weave s t (HR x) = HR (weave s t x)

sumI :: (f m a -> b) -> (g m a -> b) -> (f :+: g) m a -> b
sumI f _ (HL x) = f x
sumI _ g (HR x) = g x

-- higher-order functor isomorphism
type (f ->: g) = forall (m :: Type -> Type) k. f m k -> g m k

data (f <-> g) = Iso { to :: f ->: g, from :: g ->: f }

(<->) :: (f ->: g) -> (g ->: f) -> (f <-> g)
(<->) = Iso

isoRefl :: f <-> f
isoRefl = id <-> id

isoSym :: f <-> g -> g <-> f
isoSym i = from i <-> to i

isoTrans :: f <-> g -> g <-> h -> f <-> h
isoTrans i1 i2 = (to i2 . to i1) <-> (from i1 . from i2)

isoSumCong :: f <-> f' -> g <-> g' -> (f :+: g) <-> (f' :+: g')
isoSumCong i1 i2 = sumI (HL . to i1) (HR . to i2) <-> sumI (HL . from i1) (HR . from i2)

isoSumComm :: (f :+: g) <-> (g :+: f)
isoSumComm = sumI HR HL <-> sumI HR HL

isoSumAssoc :: (f :+: (g :+: h)) <-> ((f :+: g) :+: h)
isoSumAssoc = sumI (HL . HL) (sumI (HL . HR) HR) <-> sumI (sumI HL (HR . HL)) (HR . HR)

-- higher-order functor forephism
data HForephism f g = forall h. (HFunctor f, HFunctor g, HFunctor h) => HForephism { iso :: g <-> (f :+: h) }

infix 4 <:
class (HFunctor f, HFunctor g) => f <: g where
    forephism :: HForephism f g

injH :: (f <: g) => f m a -> g m a
injH = case forephism of
    (HForephism i) -> from i . HL

instance {-# OVERLAPPING #-} (HFunctor f) => f <: f where
    forephism :: HForephism f f
    forephism = HForephism (HL <-> sumI id (\(x :: Alg End m k) -> case x of))

instance {-# OVERLAPPING #-} (HFunctor f, HFunctor g) => f <: (f :+: g) where
    forephism :: HForephism f (f :+: g)
    forephism = HForephism isoRefl

instance {-# OVERLAPPING #-} (HFunctor f, HFunctor g, HFunctor h, f <: h) => f <: (g :+: h) where
    forephism :: f <: h => HForephism f (g :+: h)
    forephism = case forephism of
        HForephism i -> HForephism (isoTrans (isoSumCong isoRefl i) (isoTrans isoSumComm (isoSym isoSumAssoc)))

-- the lifting operation of algebraic effects to higher-order effects
newtype Alg f (m :: Type -> Type) k = Alg (f k)
    deriving Functor

instance Functor f => HFunctor (Alg f) where
    hmap :: (a ~> b) -> Alg f a ~> Alg f b
    hmap _ (Alg x) = Alg x

    weave :: (Monad m, Monad n, Functor s) => s () -> (forall x. s (m x) -> n (s x)) -> Alg f m (m a) -> Alg f n (n (s a))
    weave s f (Alg x) = Alg ((\m -> f $ m <$ s) <$> x)

injAlg :: (Functor f, Alg f <: h) => f (Hefty h a) -> Hefty h a
injAlg = Do . injH . Alg

lift :: (Functor f, Alg f <: h) => Free f a -> Hefty h a
lift = fold Return injAlg

unH :: Hefty (Alg End) a -> a
unH (Return a) = a
unH (Do op) = case op of

liftErr :: Alg Err <: h => Free Err a -> Hefty h a
liftErr = lift

infixr 6 /\
(/\) :: Algebra h1 g -> Algebra h2 g -> Algebra (h1 :+: h2) g
a1 /\ a2 = \case
    HL op -> a1 op
    HR op -> a2 op

type Elaboration h f = Algebra h (Free f)

eAlg :: a < f => Elaboration (Alg a) f
eAlg (Alg op) = Op $ inj op