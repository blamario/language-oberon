{-# Language DeriveDataTypeable, FlexibleContexts, FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses, 
             PolyKinds, RankNTypes, StandaloneDeriving, TypeFamilies, TypeOperators, UndecidableInstances #-}

module Transformation.Deep where

import Control.Applicative ((<*>))
import Data.Data (Data, Typeable)
import Data.Monoid (Monoid, (<>))
import qualified Data.Foldable
import qualified Data.Functor
import qualified Data.Traversable
import qualified Transformation as Shallow

import Prelude hiding (Foldable(..), Traversable(..), Functor(..), Applicative(..), (<$>), fst, snd)

class Functor t g (p :: * -> *) (q :: * -> *) where
   (<$>) :: t -> g p p -> g q q

class Foldable t g (p :: * -> *) m where
   foldMap :: t -> g p p -> m

class UpTraversable t g (p :: * -> *) (q :: * -> *) m where
   traverseUp :: t -> g p p -> m (g q q)

class DownTraversable t g (p :: * -> *) (q :: * -> *) m where
   traverseDown :: t -> g p p -> m (g q q)

data Product g1 g2 (p :: * -> *) (q :: * -> *) = Pair (q (g1 p p)) (q (g2 p p))

instance (Data.Functor.Functor p, Shallow.Functor t p q (g1 q q), Shallow.Functor t p q (g2 q q),
          Functor t g1 p q, Functor t g2 p q) => Functor t (Product g1 g2) p q where
   t <$> Pair left right = Pair (t Shallow.<$> ((t <$>) Data.Functor.<$> left)) 
                                (t Shallow.<$> ((t <$>) Data.Functor.<$> right))

instance (Monoid m, Data.Foldable.Foldable p,
          Foldable t g1 p m, Foldable t g2 p m) => Foldable t (Product g1 g2) p m where
   foldMap t (Pair left right) = Data.Foldable.foldMap (foldMap t) left
                                 <> Data.Foldable.foldMap (foldMap t) right

instance (Monad m, Data.Traversable.Traversable p,
          Shallow.Traversable t p q m (g1 q q), Shallow.Traversable t p q m (g2 q q),
          UpTraversable t g1 p q m, UpTraversable t g2 p q m) => UpTraversable t (Product g1 g2) p q m where
   traverseUp t (Pair left right) =
      Pair        Data.Functor.<$> (Data.Traversable.traverse (traverseUp t) left >>= Shallow.traverse t)
           Control.Applicative.<*> (Data.Traversable.traverse (traverseUp t) right >>= Shallow.traverse t)

instance (Monad m, Data.Traversable.Traversable q,
          Shallow.Traversable t p q m (g1 p p), Shallow.Traversable t p q m (g2 p p),
          DownTraversable t g1 p q m, DownTraversable t g2 p q m) => DownTraversable t (Product g1 g2) p q m where
   traverseDown t (Pair left right) =
      Pair        Data.Functor.<$> (Shallow.traverse t left >>= Data.Traversable.traverse (traverseDown t))
           Control.Applicative.<*> (Shallow.traverse t right >>= Data.Traversable.traverse (traverseDown t))

deriving instance (Typeable p, Typeable q, Typeable g1, Typeable g2,
                   Data (q (g1 p p)), Data (q (g2 p p))) => Data (Product g1 g2 p q)
deriving instance (Show (q (g1 p p)), Show (q (g2 p p))) => Show (Product g1 g2 p q)

fmap :: Functor t g p q => t -> g p p -> g q q
fmap = (<$>)
