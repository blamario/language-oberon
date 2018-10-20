{-# Language DeriveDataTypeable, FlexibleContexts, FlexibleInstances, FunctionalDependencies, MultiParamTypeClasses, 
             PolyKinds, RankNTypes, StandaloneDeriving, TypeFamilies, TypeOperators, UndecidableInstances #-}

module Transformation where

import Prelude hiding (Foldable(..), Traversable(..), Functor(..), Applicative(..), (<$>), fst, snd)

class Functor t p q x | t -> p q where
   (<$>) :: t -> p x -> q x

class Foldable t p m x | t -> p m where
   foldMap :: t -> p x -> m

class Traversable t p q m x | t -> p q m where
   traverse :: t -> p x -> m (q x)

fmap :: Functor t p q x => t -> p x -> q x
fmap = (<$>)
