{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses,
             TemplateHaskell, TypeFamilies, TypeOperators, UndecidableInstances #-}
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
import Data.Monoid (Ap(Ap, getAp))
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
   Serialization $ (s, _) = Const (Ap $ state $ f s)
      where f :: (Int, ParsedLexemes) -> (Int, [Lexeme]) -> (Text, (Int, [Lexeme]))
            f (pos, Trailing lexemes) s'@(pos', lexemes')
               | pos > pos', l:ls <- lexemes', t <- lexemeText l = first (t <>) (f s (pos' + Text.length t, ls))
               | otherwise = (mempty, (pos, lexemes <> lexemes'))

instance PositionAdjustment `Transformation.At` g Parsed Parsed where
   PositionAdjustment $ ((nodePos, Trailing nodeLexemes), node) = Compose (Ap $ state f)
      where f (pos, pos', lexemes)
               | nodePos > pos, l:ls <- lexemes, len <- Text.length (lexemeText l) = f (pos + len, pos' + len, ls)
               | otherwise = (((pos', Trailing nodeLexemes), node), (pos, pos', lexemes <> nodeLexemes))

instance (Rank2.Foldable (g Parsed), Deep.Foldable Serialization g) => Full.Foldable Serialization g where
   foldMap = Full.foldMapDownDefault

instance (Rank2.Foldable (g Parsed), Deep.Traversable PositionAdjustment g) =>
         Full.Traversable PositionAdjustment g where
   traverse = Full.traverseDownDefault
