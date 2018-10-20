{-# Language DeriveDataTypeable, FlexibleContexts, FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses, 
             PolyKinds, RankNTypes, StandaloneDeriving, TypeFamilies, TypeOperators, UndecidableInstances #-}

module Transformation.Deep where

import Data.Data (Data, Typeable)
import qualified Data.Functor
import qualified Transformation as Shallow

import Prelude hiding (Foldable(..), Traversable(..), Functor(..), Applicative(..), (<$>), fst, snd)

class Functor t g (p :: * -> *) (q :: * -> *) where
   (<$>) :: t -> g p p -> g q q

class Foldable t g (p :: * -> *) m where
   foldMap :: t -> g p p -> m

class Traversable t g (p :: * -> *) (q :: * -> *) m where
   traverse :: t -> g p p -> m (g q q)

data Product g1 g2 (p :: * -> *) (q :: * -> *) = Pair (q (g1 p p)) (q (g2 p p))

instance (Data.Functor.Functor p, Shallow.Functor t p q (g1 q q), Shallow.Functor t p q (g2 q q),
          Functor t g1 p q, Functor t g2 p q) => Functor t (Product g1 g2) p q where
   t <$> Pair left right = Pair (t Shallow.<$> ((t <$>) Data.Functor.<$> left)) 
                                (t Shallow.<$> ((t <$>) Data.Functor.<$> right))

deriving instance (Typeable p, Typeable q, Typeable g1, Typeable g2,
                   Data (q (g1 p p)), Data (q (g2 p p))) => Data (Product g1 g2 p q)
deriving instance (Show (q (g1 p p)), Show (q (g2 p p))) => Show (Product g1 g2 p q)

fmap :: Functor t g p q => t -> g p p -> g q q
fmap = (<$>)
