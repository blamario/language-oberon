{-# LANGUAGE FlexibleContexts, FlexibleInstances, KindSignatures, MultiParamTypeClasses, OverloadedStrings,
             ScopedTypeVariables, StandaloneDeriving, TemplateHaskell, TypeFamilies, TypeOperators,
             UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}

-- | This module exports functions for resolving the syntactic ambiguities in a parsed module. For example, an Oberon
-- expression @foo(bar)@ may be a call to function @foo@ with a parameter @bar@, or it may be type guard on variable
-- @foo@ casting it to type @bar@.

module Language.Oberon.Reserializer (reserialize) where

import Control.Applicative (ZipList(ZipList, getZipList))
import Control.Arrow (first)
import Control.Monad.Trans.State (StateT(..), evalStateT, execStateT, get, put)
import Data.Either (partitionEithers)
import Data.Either.Validation (Validation(..), validationToEither)
import Data.Foldable (toList)
import Data.Functor.Const (Const(..))
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.List as List
import Data.Map.Lazy (Map, traverseWithKey)
import qualified Data.Map.Lazy as Map
import Data.Semigroup (Semigroup(..), sconcat)
import Data.Text (Text)
import qualified Data.Text as Text

import qualified Rank2
import qualified Transformation
import qualified Transformation.Deep as Deep
import qualified Transformation.Deep.TH
import qualified Transformation.Full as Full
import qualified Transformation.Full.TH

import qualified Language.Oberon.Abstract as Abstract
import Language.Oberon.AST
import Language.Oberon.Grammar (ParsedLexemes(Trailing), Lexeme(..))

reserialize :: Deep.Foldable Serialization g => Parsed (g Parsed Parsed) -> Text
reserialize = finalize . (`runState` (0, [])) . Full.foldMap Serialization
   where finalize (s, (_pos, rest)) = s <> foldMap lexemeText rest

type Parsed = (,) (Int, ParsedLexemes)

data Serialization = Serialization

newtype State s a = State {runState :: s -> (a, s)}

instance Semigroup a => Semigroup (State s a) where
   State f1 <> State f2 = State f'
      where f' s0 = let (a1, s1) = f1 s0
                        (a2, s2) = f2 s1
                    in (a1 <> a2, s2)

instance Monoid a => Monoid (State s a) where
   mempty = State (\s-> (mempty, s))

instance Transformation.Transformation Serialization where
    type Domain Serialization = Parsed
    type Codomain Serialization = Const (State (Int, [Lexeme]) Text)

instance Serialization `Transformation.At` g Parsed Parsed where
   Serialization $ (s, _) = Const (State $ f s)
      where f :: (Int, ParsedLexemes) -> (Int, [Lexeme]) -> (Text, (Int, [Lexeme]))
            f (pos, Trailing lexemes) s'@(pos', lexemes')
               | pos > pos', l:ls <- lexemes', t <- lexemeText l = first (t <>) (f s (pos' + Text.length t, ls))
               | otherwise = (mempty, (pos, lexemes <> lexemes'))

instance (Rank2.Foldable (g Parsed), Deep.Foldable Serialization g) => Full.Foldable Serialization g where
   foldMap = Full.foldMapDownDefault
