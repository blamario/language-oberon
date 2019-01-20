{-# Language DefaultSignatures, FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, StandaloneDeriving,
             TypeFamilies, TypeOperators, UndecidableInstances #-}

module Transformation.AG where

import Data.Functor.Identity
import qualified Rank2
import qualified Transformation as Shallow
import qualified Transformation.Deep as Deep

data Inherited a g = Inherited{inh :: Atts (Inherited a) g}
data Synthesized a g = Synthesized{syn :: Atts (Synthesized a) g}

type family Atts (f :: * -> *) x
deriving instance (Show (Atts (Inherited a) g)) => Show (Inherited a g)
deriving instance (Show (Atts (Synthesized a) g)) => Show (Synthesized a g)
-- type instance Atts Identity f = f Identity
-- type instance Atts (Inherited a Rank2.~> Synthesized a) g = Atts (Inherited a) g -> Atts (Synthesized a) g

type Semantics a = Inherited a Rank2.~> Synthesized a

type Rule a g (f :: * -> *) = g f (Semantics a)
                           -> (Inherited   a (g f (Semantics a)), g f (Synthesized a))
                           -> (Synthesized a (g f (Semantics a)), g f (Inherited a))

knit :: Rank2.Apply (g f) => Rule a g f -> g f (Semantics a) -> Semantics a (g f (Semantics a))
knit r chSem = Rank2.Arrow knit'
   where knit' inh = syn
            where (syn, chInh) = r chSem (inh, chSyn)
                  chSyn = chSem Rank2.<*> chInh

class Shallow.Functor t Identity (Semantics t) (g (Semantics t) (Semantics t)) => Attribution t g where
   attribution :: t -> Rule t g (Semantics t)

mapDefault :: (q ~ Semantics t, x ~ g q q, Rank2.Apply (g q), Attribution t g) => (p x -> x) -> t -> p x -> q x
mapDefault extract t sem = knit (attribution t) (extract sem)
{-# INLINE mapDefault #-}
