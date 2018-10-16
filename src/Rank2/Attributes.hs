{-# Language DeriveDataTypeable, FlexibleContexts, FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses, 
             PolyKinds, RankNTypes, StandaloneDeriving, TypeFamilies, TypeOperators, UndecidableInstances #-}

module Rank2.Attributes where

import Data.Data (Data, Typeable)
import Data.Functor.Identity
import qualified Rank2

type family Atts (f :: * -> *) x

data Inherited a g = Inherited{inh :: Atts (Inherited a) g}
data Synthesized a g = Synthesized{syn :: Atts (Synthesized a) g}

type Semantics a = Inherited a Rank2.~> Synthesized a

type Rule a g (f :: * -> *) = (Inherited   a (g f (Semantics a)), g f (Synthesized a))
                           -> (Synthesized a (g f (Semantics a)), g f (Inherited a))

class Transformation t p q x | t -> p q where
   remap :: t -> p x -> q x

class DeepTransformation t g (p :: * -> *) (q :: * -> *) where
   deepmap :: t -> g p p -> g q q

class Transformation t Identity (Semantics t) (g (Semantics t) (Semantics t)) => Attribution t g where
   attribution :: t -> Rule t g (Semantics t)

instance Transformation (Rank2.Arrow p q x) p q x where
   remap = Rank2.apply

newtype Arrow p q = Arrow (forall x. Rank2.Arrow p q x)

instance Transformation (Arrow p q) p q x where
   remap (Arrow a) = Rank2.apply a

dmap :: DeepTransformation (Arrow p q) g p q => (forall a. p a -> q a) -> g p p -> g q q
dmap f g = deepmap (Arrow $ Rank2.Arrow f) g

knit :: Rank2.Apply (g f)
     => Rule a g f -> g f (Semantics a) -> Inherited a (g f (Semantics a)) -> Synthesized a (g f (Semantics a))
knit r chSem inh = syn
   where (syn, chInh) = r (inh, chSyn)
         chSyn = chSem Rank2.<*> chInh

knitmap :: (p ~ Identity, q ~ Semantics t, x ~ g q q, Rank2.Apply (g q), Attribution t g)
        => t -> Identity x -> Semantics t x
knitmap t (Identity sem) = Rank2.Arrow (knit (attribution t) sem)

data Product g1 g2 (p :: * -> *) (q :: * -> *) = Pair (q (g1 p p)) (q (g2 p p))

instance (Functor p, Transformation t p q (g1 q q), Transformation t p q (g2 q q), 
          DeepTransformation t g1 p q, DeepTransformation t g2 p q) => DeepTransformation t (Product g1 g2) p q where
   deepmap t (Pair left right) = Pair (remap t $ deepmap t <$> left) (remap t $ deepmap t <$> right)

deriving instance (Typeable p, Typeable q, Typeable g1, Typeable g2,
                   Data (q (g1 p p)), Data (q (g2 p p))) => Data (Product g1 g2 p q)
deriving instance (Show (q (g1 p p)), Show (q (g2 p p))) => Show (Product g1 g2 p q)
