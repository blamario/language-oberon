{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses,
             ScopedTypeVariables, TemplateHaskell, TypeFamilies, TypeOperators, UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}

-- | This module exports functions for reserializing the parsed tree from the tokens stored with every node.

module Language.Oberon.Reserializer (adjustPositions, reserialize, sourceLength, PositionAdjustment, Serialization) where

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
import qualified Transformation.Rank2
import qualified Transformation.Deep as Deep
import qualified Transformation.Full as Full

import qualified Language.Oberon.Abstract as Abstract
import Language.Oberon.AST
import Language.Oberon.Grammar (ParsedLexemes(Trailing), Lexeme(..))

-- | Re-calculates the position of every node in the parse tree from the tokens stored with it and its children.
adjustPositions :: (Rank2.Foldable (g (Const (Sum Int))),
                    Deep.Foldable (Transformation.Rank2.Fold Parsed (Sum Int)) g,
                    Deep.Traversable PositionAdjustment g) => Parsed (g Parsed Parsed) -> Parsed (g Parsed Parsed)
adjustPositions node@((pos, _, _), _) = evalState (Full.traverse PositionAdjustment node) 0

-- | Serializes the tree back into the text it was parsed from.
reserialize :: Deep.Foldable Serialization g => Parsed (g Parsed Parsed) -> Text
reserialize = finalize . (`runState` (0, [])) . getAp . Full.foldMap Serialization
   where finalize (s, (_pos, rest)) = s <> foldMap lexemeText rest

-- | The length of the source code parsed into the argument node
sourceLength :: (Rank2.Foldable (g (Const (Sum Int))),
                 Deep.Foldable (Transformation.Rank2.Fold Parsed (Sum Int)) g) => Parsed (g Parsed Parsed) -> Int
sourceLength root@((_, Trailing rootLexemes, _), node) = getSum (nodeLength root
                                                                 <> Transformation.Rank2.foldMap nodeLength node)
   where nodeLength ((_, Trailing lexemes, _), _) = foldMap (Sum . Text.length . lexemeText) lexemes

type Parsed = (,) (Int, ParsedLexemes, Int)

-- | Transformation type used by 'reserialize'
data Serialization = Serialization
-- | Transformation type used by 'adjustPositions'
data PositionAdjustment = PositionAdjustment

instance Transformation.Transformation Serialization where
    type Domain Serialization = Parsed
    type Codomain Serialization = Const (Ap (State (Int, [Lexeme])) Text)

instance Transformation.Transformation PositionAdjustment where
    type Domain PositionAdjustment = Parsed
    type Codomain PositionAdjustment = Compose (State Int) Parsed

instance Serialization `Transformation.At` g Parsed Parsed where
   Serialization $ ((nodePos, Trailing nodeLexemes, _), _) = Const (Ap $ state f)
      where f :: (Int, [Lexeme]) -> (Text, (Int, [Lexeme]))
            f (pos, lexemes)
               | nodePos > pos, l:ls <- lexemes, t <- lexemeText l = first (t <>) (f (pos + Text.length t, ls))
               | otherwise = (mempty, (pos, nodeLexemes <> lexemes))

instance (Rank2.Foldable (g Parsed), Deep.Foldable Serialization g) => Full.Foldable Serialization g where
   foldMap trans ((nodeStart, Trailing nodeLexemes, _), node) = Ap (state f)
      where f :: (Int, [Lexeme]) -> (Text, (Int, [Lexeme]))
            f (pos, lexemes)
               | nodeStart > pos, l:ls <- lexemes, t <- lexemeText l = first (t <>) (f (pos + Text.length t, ls))
               | otherwise = let (t, (pos', lexemes')) = runState (getAp $ Deep.foldMap trans node) (pos, nodeLexemes)
                                 t' = foldMap lexemeText lexemes'
                             in (t <> t', (pos' + Text.length t', lexemes))

instance (Rank2.Foldable (g (Const (Sum Int))),
          Deep.Foldable (Transformation.Rank2.Fold Parsed (Sum Int)) g) =>
         PositionAdjustment `Transformation.At` g Parsed Parsed where
   PositionAdjustment $ root@((nodeStart, lexemes, nodeEnd), node) = Compose (state f)
      where f adjustment = (((nodeStart + adjustment, lexemes, nodeEnd' + adjustment), node),
                            adjustment + nodeEnd' - nodeEnd)
               where nodeEnd' = nodeStart + sourceLength root

instance (Rank2.Foldable (g (Const (Sum Int))),
          Rank2.Traversable (g Parsed),
          Deep.Foldable (Transformation.Rank2.Fold Parsed (Sum Int)) g,
          Deep.Traversable PositionAdjustment g) => Full.Traversable PositionAdjustment g where
   traverse PositionAdjustment root@((nodeStart, lexemes, nodeEnd), node) = state f
      where f adjustment = (((nodeStart + adjustment, lexemes, nodeEnd' + adjustment),
                             evalState (Deep.traverse PositionAdjustment node) adjustment),
                            adjustment + nodeEnd' - nodeEnd)
               where nodeEnd' = nodeStart + sourceLength root

instance (Rank2.Foldable (g Parsed),
          Deep.Foldable (Transformation.Rank2.Fold Parsed (Sum Int)) g) =>
         Full.Foldable (Transformation.Rank2.Fold Parsed (Sum Int)) g where
   foldMap = Full.foldMapDownDefault
