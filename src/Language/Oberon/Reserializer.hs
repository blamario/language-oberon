{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses,
             ScopedTypeVariables, TemplateHaskell, TypeFamilies, TypeOperators, UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}

-- | This module exports functions for resolving the syntactic ambiguities in a parsed module. For example, an Oberon
-- expression @foo(bar)@ may be a call to function @foo@ with a parameter @bar@, or it may be type guard on variable
-- @foo@ casting it to type @bar@.

module Language.Oberon.Reserializer (adjustPositions, reserialize) where

import Control.Arrow (first)
import Control.Monad.Trans.State.Strict (State, StateT(..), evalState, runState, state)
import Data.Either (partitionEithers)
import Data.Either.Validation (Validation(..), validationToEither)
import Data.Foldable (toList)
import Data.Functor.Compose (Compose(..))
import Data.Functor.Const (Const(..))
import Data.Monoid (Ap(Ap, getAp), Sum(Sum, getSum))
import Data.Text (Text)
import qualified Data.Text as Text

import qualified Rank2
import qualified Transformation
import qualified Transformation.Deep as Deep
import qualified Transformation.Full as Full

import qualified Language.Oberon.Abstract as Abstract
import Language.Oberon.AST
import Language.Oberon.Grammar (ParsedLexemes(Trailing), Lexeme(..))

adjustPositions :: Deep.Traversable PositionAdjustment g => Parsed (g Parsed Parsed) -> Parsed (g Parsed Parsed)
adjustPositions node@((pos, _), _) = evalState (getAp $ Full.traverse PositionAdjustment node) (pos, pos, [])

reserialize :: Deep.Foldable Serialization g => Parsed (g Parsed Parsed) -> Text
reserialize = finalize . (`runState` (0, [])) . getAp . Full.foldMap Serialization
   where finalize (s, (_pos, rest)) = s <> foldMap lexemeText rest

type Parsed = (,) (Int, ParsedLexemes)

data Serialization = Serialization
data PositionAdjustment = PositionAdjustment

instance Transformation.Transformation Serialization where
    type Domain Serialization = Parsed
    type Codomain Serialization = Const (Ap (State (Int, [Lexeme])) Text)

instance Transformation.Transformation PositionAdjustment where
    type Domain PositionAdjustment = Parsed
    type Codomain PositionAdjustment = Compose (Ap (State (Int, Int, [Lexeme]))) Parsed

instance Serialization `Transformation.At` g Parsed Parsed where
   Serialization $ ((nodePos, Trailing nodeLexemes), _) = Const (Ap $ state f)
      where f :: (Int, [Lexeme]) -> (Text, (Int, [Lexeme]))
            f (pos, lexemes)
               | nodePos > pos, l:ls <- lexemes, t <- lexemeText l = first (t <>) (f (pos + Text.length t, ls))
               | otherwise = (mempty, (pos, nodeLexemes <> lexemes))

instance PositionAdjustment `Transformation.At` g Parsed Parsed where
   PositionAdjustment $ ((nodePos, Trailing nodeLexemes), node) = Compose (Ap $ state f)
      where f (pos, pos', lexemes)
               | nodePos > pos, l:ls <- lexemes, len <- Text.length (lexemeText l) = f (pos + len, pos' + len, ls)
               | otherwise = (((pos', Trailing nodeLexemes), node), (pos, pos', lexemes <> nodeLexemes))

instance (Rank2.Foldable (g Parsed), Deep.Foldable Serialization g) => Full.Foldable Serialization g where
   foldMap trans ((nodePos, Trailing nodeLexemes), node) = Ap (state f)
      where f :: (Int, [Lexeme]) -> (Text, (Int, [Lexeme]))
            f (pos, lexemes)
               | nodePos > pos, l:ls <- lexemes, t <- lexemeText l = first (t <>) (f (pos + Text.length t, ls))
               | otherwise = let (t, (pos', lexemes')) = runState (getAp $ Deep.foldMap trans node) (pos, nodeLexemes)
                                 t' = foldMap lexemeText lexemes'
                             in (t <> t', (pos' + Text.length t', lexemes))

instance (Rank2.Foldable (g Parsed), Deep.Traversable PositionAdjustment g) =>
         Full.Traversable PositionAdjustment g where
   traverse trans ((nodePos0, Trailing nodeLexemes), node) = Ap (state $ f nodePos0)
      where f :: Int -> (Int, Int, [Lexeme]) -> (Parsed (g Parsed Parsed), (Int, Int, [Lexeme]))
            f nodePos (pos, pos', lexemes)
               | nodePos0 > pos, l:ls <- lexemes,
                 len <- Text.length (lexemeText l) = f (nodePos + len) (pos + len, pos' + len, ls)
               | otherwise = let (node', (pos1, pos1', lexemes')) =
                                    runState (getAp $ Deep.traverse trans node) (pos, pos', nodeLexemes)
                                 Sum len = foldMap (Sum . Text.length . lexemeText) lexemes'
                             in (((pos', Trailing nodeLexemes), node'), (nodePos + len, pos1' + len, lexemes))
