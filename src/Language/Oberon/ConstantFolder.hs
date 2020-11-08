{-# LANGUAGE DataKinds, DeriveGeneric, DuplicateRecordFields, FlexibleContexts, FlexibleInstances,
             MultiParamTypeClasses, OverloadedStrings, RankNTypes, ScopedTypeVariables,
             TemplateHaskell, TypeFamilies, UndecidableInstances #-}

-- | The main export of this module is the function 'foldConstants' that folds the constants in Oberon AST using a
-- attribute grammar. Other exports are helper functions and attribute types that can be reused for other languages or
-- attribute grammars.
-- 
-- This module expects the ambiguities in the AST to be already resolved by the "Language.Oberon.Resolver" module.

module Language.Oberon.ConstantFolder where

import Control.Applicative (liftA2, ZipList(ZipList, getZipList))
import Control.Arrow (first)
import Control.Monad (join)
import Data.Bits (shift)
import Data.Char (chr, ord, toUpper)
import Data.Functor.Identity (Identity(..))
import Data.Int (Int32)
import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as Map
import Data.Semigroup (Semigroup(..))
import qualified Data.Text as Text
import Foreign.Storable (sizeOf)
import GHC.Generics (Generic)
import Language.Haskell.TH (appT, conT, varT, varE, newName)
import Data.Text.Prettyprint.Doc (layoutCompact, Pretty(pretty))
import Data.Text.Prettyprint.Doc.Render.Text (renderStrict)

import qualified Rank2
import qualified Transformation
import qualified Transformation.Rank2
import qualified Transformation.Deep as Deep
import qualified Transformation.Full as Full
import qualified Transformation.Full.TH
import qualified Transformation.Shallow as Shallow
import qualified Transformation.AG as AG
import Transformation.AG (Attribution(..), Atts, Inherited(..), Synthesized(..), Semantics)
import Transformation.AG.Generics (Auto(Auto), Bequether(..), Synthesizer(..), SynthesizedField(..), Mapped(..))

import qualified Language.Oberon.Abstract as Abstract
import qualified Language.Oberon.AST as AST
import qualified Language.Oberon.Pretty ()
import Language.Oberon.Grammar (ParsedLexemes(Trailing), Lexeme(Token, WhiteSpace, lexemeType, lexemeText),
                                TokenType(Other))

-- | Fold the constants in the given collection of Oberon modules (a 'Map' of modules keyed by module name). It uses
-- the constant declarations from the modules as well as the given 'Environment' of predefined constants and
-- functions. The value of the latter argument is typically 'predefined' or 'predefined2'.
foldConstants :: (Abstract.Oberon l, Abstract.Nameable l,
                  Ord (Abstract.QualIdent l), Show (Abstract.QualIdent l),
                  Atts (Inherited (Auto ConstantFold)) (Abstract.Block l l Sem Sem) ~ InhCF l,
                  Atts (Synthesized (Auto ConstantFold)) (Abstract.Block l l Sem Sem)
                  ~ SynCFMod' l (Abstract.Block l l),
                  Full.Functor (Auto ConstantFold) (Abstract.Block l l),
                  Deep.Functor (Auto ConstantFold) (Abstract.Block l l))
              => Environment l -> Map AST.Ident (Placed (AST.Module l l Placed Placed))
              -> Map AST.Ident (Placed (AST.Module l l Placed Placed))
foldConstants predef modules =
   getModules (modulesFolded $
               syn (Transformation.apply (Auto ConstantFold)
                                         (wrap (Auto ConstantFold Deep.<$> Modules modules))
                    `Rank2.apply`
                    Inherited (InhCFRoot predef)))
   where wrap = (,) (0, Trailing [], 0)

type Placed = (,) (Int, ParsedLexemes, Int)

type Environment l = Map (Abstract.QualIdent l) (Maybe (Abstract.Value l l Placed Placed))

newtype Modules l f' f = Modules {getModules :: Map AST.Ident (f (AST.Module l l f' f'))}

data ConstantFold = ConstantFold

type Sem = Semantics (Auto ConstantFold)

instance Transformation.Transformation (Auto ConstantFold) where
   type Domain (Auto ConstantFold) = Placed
   type Codomain (Auto ConstantFold) = Semantics (Auto ConstantFold)

data InhCFRoot l = InhCFRoot{rootEnv :: Environment l} deriving Generic

data InhCF l = InhCF{env           :: Environment l,
                     currentModule :: AST.Ident}
               deriving Generic

data SynCF a = SynCF{folded :: Mapped Placed a} deriving Generic

data SynCFMod l a = SynCFMod{moduleEnv :: Environment l,
                             folded    :: Mapped Placed a}
                    deriving Generic

data SynCFExp λ l = SynCFExp{folded   :: Mapped Placed (Abstract.Expression λ l Placed Placed),
                             foldedValue :: Maybe (Placed (Abstract.Value l l Placed Placed))}

data SynCFDesignator l = SynCFDesignator{folded :: Mapped Placed (Abstract.Designator l l Placed Placed),
                                         designatorValue :: Maybe (Placed (Abstract.Value l l Placed Placed))}
                         deriving Generic

data SynCFRoot a = SynCFRoot{modulesFolded :: a}

-- * Modules instances, TH candidates
instance (Transformation.Transformation t, Functor (Transformation.Domain t), Deep.Functor t (AST.Module l l),
          Transformation.At t (AST.Module l l (Transformation.Codomain t) (Transformation.Codomain t))) =>
         Deep.Functor t (Modules l) where
   t <$> ~(Modules ms) = Modules (mapModule <$> ms)
      where mapModule m = t Transformation.$ ((t Deep.<$>) <$> m)

instance Rank2.Functor (Modules l f') where
   f <$> ~(Modules ms) = Modules (f <$> ms)

instance Rank2.Apply (Modules l f') where
   ~(Modules fs) <*> ~(Modules ms) = Modules (Map.intersectionWith Rank2.apply fs ms)

instance (Transformation.Transformation t, Transformation.At t (AST.Module l l f f)) =>
         Shallow.Functor t (Modules l f) where
   t <$> ~(Modules ms) = Modules ((t Transformation.$) <$> ms)

-- * Boring attribute types
type instance Atts (Synthesized (Auto ConstantFold)) (Modules l _ _) = SynCFRoot (Modules l Placed Placed)
type instance Atts (Synthesized (Auto ConstantFold)) (AST.Module l l _ _) = SynCFMod' l (AST.Module l l)
type instance Atts (Synthesized (Auto ConstantFold)) (AST.Declaration l l _ _) = SynCFMod' l (AST.Declaration l l)
type instance Atts (Synthesized (Auto ConstantFold)) (AST.ProcedureHeading l l _ _) = SynCF' (AST.ProcedureHeading l l)
type instance Atts (Synthesized (Auto ConstantFold)) (AST.Block l l _ _) = SynCFMod' l (AST.Block l l)
type instance Atts (Synthesized (Auto ConstantFold)) (AST.FormalParameters l l _ _) = SynCF' (AST.FormalParameters l l)
type instance Atts (Synthesized (Auto ConstantFold)) (AST.FPSection l l _ _) = SynCF' (AST.FPSection l l)
type instance Atts (Synthesized (Auto ConstantFold)) (AST.Type l l _ _) = SynCF' (AST.Type l l)
type instance Atts (Synthesized (Auto ConstantFold)) (AST.FieldList l l _ _) = SynCF' (AST.FieldList l l)
type instance Atts (Synthesized (Auto ConstantFold)) (AST.StatementSequence l l _ _) =
   SynCF' (AST.StatementSequence l l)
type instance Atts (Synthesized (Auto ConstantFold)) (AST.Expression λ l _ _) = SynCFExp λ l
type instance Atts (Synthesized (Auto ConstantFold)) (AST.Element l l _ _) = SynCF' (AST.Element l l)
type instance Atts (Synthesized (Auto ConstantFold)) (AST.Value l l _ _) = SynCF' (AST.Value l l)
type instance Atts (Synthesized (Auto ConstantFold)) (AST.Designator l l _ _) = SynCFDesignator l
type instance Atts (Synthesized (Auto ConstantFold)) (AST.Statement l l _ _) = SynCF' (AST.Statement l l)
type instance Atts (Synthesized (Auto ConstantFold)) (AST.Case l l _ _) = SynCF' (AST.Case l l)
type instance Atts (Synthesized (Auto ConstantFold)) (AST.CaseLabels l l _ _) = SynCF' (AST.CaseLabels l l)
type instance Atts (Synthesized (Auto ConstantFold)) (AST.ConditionalBranch l l _ _) =
   SynCF' (AST.ConditionalBranch l l)
type instance Atts (Synthesized (Auto ConstantFold)) (AST.WithAlternative l l _ _) = SynCF' (AST.WithAlternative l l)

type instance Atts (Inherited (Auto ConstantFold)) (Modules l _ _) = InhCFRoot l
type instance Atts (Inherited (Auto ConstantFold)) (AST.Module l l _ _) = InhCF l
type instance Atts (Inherited (Auto ConstantFold)) (AST.Declaration l l _ _) = InhCF l
type instance Atts (Inherited (Auto ConstantFold)) (AST.ProcedureHeading l l _ _) = InhCF l
type instance Atts (Inherited (Auto ConstantFold)) (AST.Block l l _ _) = InhCF l
type instance Atts (Inherited (Auto ConstantFold)) (AST.FormalParameters l l _ _) = InhCF l
type instance Atts (Inherited (Auto ConstantFold)) (AST.FPSection l l _ _) = InhCF l
type instance Atts (Inherited (Auto ConstantFold)) (AST.Type l l _ _) = InhCF l
type instance Atts (Inherited (Auto ConstantFold)) (AST.FieldList l l _ _) = InhCF l
type instance Atts (Inherited (Auto ConstantFold)) (AST.StatementSequence l l _ _) = InhCF l
type instance Atts (Inherited (Auto ConstantFold)) (AST.Expression l l _ _) = InhCF l
type instance Atts (Inherited (Auto ConstantFold)) (AST.Element l l _ _) = InhCF l
type instance Atts (Inherited (Auto ConstantFold)) (AST.Value l l _ _) = InhCF l
type instance Atts (Inherited (Auto ConstantFold)) (AST.Designator l l _ _) = InhCF l
type instance Atts (Inherited (Auto ConstantFold)) (AST.Statement l l _ _) = InhCF l
type instance Atts (Inherited (Auto ConstantFold)) (AST.Case l l _ _) = InhCF l
type instance Atts (Inherited (Auto ConstantFold)) (AST.CaseLabels l l _ _) = InhCF l
type instance Atts (Inherited (Auto ConstantFold)) (AST.ConditionalBranch l l _ _) = InhCF l
type instance Atts (Inherited (Auto ConstantFold)) (AST.WithAlternative l l _ _) = InhCF l

type SynCF' node = SynCF (node Placed Placed)
type SynCFMod' l node = SynCFMod l (node Placed Placed)


-- * Disambiguation

folded' :: SynCF' node -> Mapped Placed (node Placed Placed)
foldedExp  :: SynCFExp λ l -> Mapped Placed (Abstract.Expression λ l Placed Placed)
foldedExp' :: SynCFExp λ l -> Placed (Abstract.Expression λ l Placed Placed)

folded' = folded
foldedExp = folded
foldedExp' = getMapped . foldedExp

-- * Rules

instance {-# overlaps #-} Ord (Abstract.QualIdent l) =>
                          Synthesizer (Auto ConstantFold) (Modules l) Sem Placed where
   synthesis _ (_, Modules self) inheritance (Modules ms) =
      SynCFRoot{modulesFolded= (Modules (getMapped . foldedModule . syn <$> ms))}
      where foldedModule :: SynCFMod' l (AST.Module l l) -> Mapped Placed (AST.Module l l Placed Placed)
            foldedModule = folded

instance {-# overlaps #-} Ord (Abstract.QualIdent l) =>
                          Bequether (Auto ConstantFold) (Modules l) Sem Placed where
   bequest _ (_, Modules self) inheritance (Modules ms) = Modules (Map.mapWithKey moduleInheritance self)
      where moduleInheritance name mod = Inherited InhCF{env= rootEnv inheritance <> foldMap (moduleEnv . syn) ms,
                                                         currentModule= name}

instance {-# overlaps #-} (Abstract.Oberon l, Abstract.Nameable l, Ord (Abstract.QualIdent l), Show (Abstract.QualIdent l),
                           Atts (Synthesized (Auto ConstantFold)) (Abstract.Block l l Sem Sem) ~ SynCFMod' l (Abstract.Block l l)) =>
                          Synthesizer (Auto ConstantFold) (AST.Module l l) Sem Placed where
   synthesis _ (pos, AST.Module moduleName imports _body) inheritance (AST.Module _ _ body) =
      SynCFMod{moduleEnv= exportedEnv,
               folded= Mapped (pos,
                               AST.Module moduleName imports $ getMapped
                               $ folded (syn body :: SynCFMod' l (Abstract.Block l l)))}
      where exportedEnv = Map.mapKeysMonotonic export newEnv
            newEnv = moduleEnv (syn body)
            export q
               | Just name <- Abstract.getNonQualIdentName q = Abstract.qualIdent moduleName name
               | otherwise = q

instance (Abstract.Nameable l, Ord (Abstract.QualIdent l),
          Atts (Synthesized (Auto ConstantFold)) (Abstract.Declaration l l Sem Sem) ~ SynCFMod' l (Abstract.Declaration l l),
          Atts (Inherited (Auto ConstantFold)) (Abstract.StatementSequence l l Sem Sem) ~ InhCF l,
          Atts (Inherited (Auto ConstantFold)) (Abstract.Declaration l l Sem Sem) ~ InhCF l) =>
         Bequether (Auto ConstantFold) (AST.Block l l) Sem Placed where
   bequest _ (pos, AST.Block _decls _stats) inheritance (AST.Block decls stats) =
      AST.Block (pure $ Inherited localEnv) (pure $ Inherited localEnv)
      where newEnv = Map.unions (moduleEnv . syn <$> decls)
            localEnv = InhCF (newEnv `Map.union` env inheritance) (currentModule inheritance)

instance (Abstract.Nameable l, k ~ Abstract.QualIdent l, v ~ Abstract.Value l l Placed Placed, Ord k,
          Atts (Synthesized (Auto ConstantFold)) (Abstract.Declaration l l Sem Sem)
          ~ SynCFMod' l (Abstract.Declaration l l)) =>
         SynthesizedField "moduleEnv" (Map k (Maybe v)) (Auto ConstantFold) (AST.Block l l) Sem Placed where
   synthesizedField _ _ (_, AST.Block{}) _ (AST.Block decls _stats) = Map.unions (moduleEnv . syn <$> decls)

instance (Abstract.Nameable l, k ~ Abstract.QualIdent l, v ~ Abstract.Value l l Placed Placed, Ord k,
          Atts (Synthesized (Auto ConstantFold)) (Abstract.ConstExpression l l Sem Sem) ~ SynCFExp l l) =>
         SynthesizedField "moduleEnv" (Map k (Maybe v)) (Auto ConstantFold) (AST.Declaration l l) Sem Placed where
   synthesizedField _ _ (_, AST.ConstantDeclaration namedef _) _ (AST.ConstantDeclaration _ expression) =
      Map.singleton (Abstract.nonQualIdent $ Abstract.getIdentDefName namedef)
                    ((snd <$>) . foldedValue $ syn expression)
   synthesizedField _ _ _ _ _ = mempty

instance {-# overlaps #-}
   (Abstract.Oberon l, Abstract.Nameable l, Ord (Abstract.QualIdent l),
    Abstract.Value l ~ AST.Value l, InhCF l ~ InhCF λ,
    Pretty (AST.Value λ λ Identity Identity),
    Atts (Synthesized (Auto ConstantFold)) (Abstract.Expression l l Sem Sem) ~ SynCFExp l l,
    Atts (Synthesized (Auto ConstantFold)) (Abstract.Element l l Sem Sem) ~ SynCF' (Abstract.Element l l),
    Atts (Synthesized (Auto ConstantFold)) (Abstract.Designator l l Sem Sem) ~ SynCFDesignator l) =>
   Synthesizer (Auto ConstantFold) (AST.Expression λ l) Sem Placed where
   synthesis _ (pos@(start, _, end), AST.Relation op _ _) _ (AST.Relation _op left right) =
      case join (compareValues <$> foldedValue (syn left) <*> foldedValue (syn right))
      of Just value -> literalSynthesis value
         Nothing -> SynCFExp{folded= Mapped (pos,
                                             Abstract.relation op (foldedExp' $ syn left) (foldedExp' $ syn right)),
                             foldedValue= Nothing}
      where compareValues (_, AST.Boolean l) (ls, AST.Boolean r)   = repos ls <$> relate op (compare l r)
            compareValues (_, AST.Integer l) (ls, AST.Integer r)   = repos ls <$> relate op (compare l r)
            compareValues (_, AST.Real l) (ls, AST.Real r)         = repos ls <$> relate op (compare l r)
            compareValues (_, AST.Integer l) (ls, AST.Real r)      = repos ls <$> relate op (compare (fromIntegral l) r)
            compareValues (_, AST.Real l) (ls, AST.Integer r)      = repos ls <$> relate op (compare l (fromIntegral r))
            compareValues (_, AST.CharCode l) (ls, AST.CharCode r) = repos ls <$> relate op (compare l r)
            compareValues (_, AST.String l) (ls, AST.String r)     = repos ls <$> relate op (compare l r)
            compareValues (_, AST.CharCode l) (ls, AST.String r) = repos ls
                                                                   <$> relate op (compare (Text.singleton $ chr l) r)
            compareValues (_, AST.String l) (ls, AST.CharCode r) = repos ls
                                                                   <$> relate op (compare l (Text.singleton $ chr r))
            compareValues _ _                               = Nothing
            repos (_, ls, _) v = ((start, ls, end), v)
            relate Abstract.Equal EQ          = Just Abstract.true
            relate Abstract.Equal _           = Just Abstract.false
            relate Abstract.Unequal EQ        = Just Abstract.false
            relate Abstract.Unequal _         = Just Abstract.true
            relate Abstract.Less LT           = Just Abstract.true
            relate Abstract.Less _            = Just Abstract.false
            relate Abstract.LessOrEqual GT    = Just Abstract.false
            relate Abstract.LessOrEqual _     = Just Abstract.true
            relate Abstract.Greater GT        = Just Abstract.true
            relate Abstract.Greater _         = Just Abstract.false
            relate Abstract.GreaterOrEqual LT = Just Abstract.false
            relate Abstract.GreaterOrEqual _  = Just Abstract.true
            relate Abstract.In _              = Nothing
   synthesis _ (pos@(start, _, end), _) _ (AST.Positive expr) =
      case foldedValue (syn expr)
      of Just ((_, ls, _), AST.Integer n) -> literalSynthesis ((start, ls, end), AST.Integer n)
         Just ((_, ls, _), AST.Real n) -> literalSynthesis ((start, ls, end), AST.Real n)
         _ -> SynCFExp{folded= Mapped (pos, Abstract.positive $ foldedExp' $ syn expr),
                       foldedValue= Nothing}
   synthesis _ (pos@(start, _, end), _) _ (AST.Negative expr) =
      case foldedValue (syn expr)
      of Just ((_, ls, _), AST.Integer n) -> literalSynthesis ((start, ls, end), AST.Integer $ negate n)
         Just ((_, ls, _), AST.Real n) -> literalSynthesis ((start, ls, end), AST.Real $ negate n)
         _ -> SynCFExp{folded= Mapped (pos, Abstract.negative $ foldedExp' $ syn expr),
                       foldedValue= Nothing}
   synthesis _ (pos, _) _ (AST.Add left right) =
      foldBinaryArithmetic pos Abstract.add (+) (syn left) (syn right)
   synthesis _ (pos, _) _ (AST.Subtract left right) =
      foldBinaryArithmetic pos Abstract.subtract (-) (syn left) (syn right)
   synthesis _ (pos, _) _ (AST.Or left right) =
      foldBinaryBoolean pos Abstract.or (||) (syn left) (syn right)
   synthesis _ (pos, _) _ (AST.Multiply left right) =
      foldBinaryArithmetic pos Abstract.multiply (*) (syn left) (syn right)
   synthesis _ (pos, _) _ (AST.Divide left right) =
      foldBinaryFractional pos Abstract.divide (/) (syn left) (syn right)
   synthesis _ (pos, _) _ (AST.IntegerDivide left right) =
      foldBinaryInteger pos Abstract.integerDivide div (syn left) (syn right)
   synthesis _ (pos, _) _ (AST.Modulo left right) =
      foldBinaryInteger pos Abstract.modulo mod (syn left) (syn right)
   synthesis _ (pos, _) _ (AST.And left right) =
      foldBinaryBoolean pos Abstract.and (&&) (syn left) (syn right)
   synthesis _ (pos@(start, _, end), _) _ (AST.Not expr) =
      case foldedValue (syn expr)
      of Just ((_, ls, _), AST.Boolean True) -> literalSynthesis ((start, ls, end), Abstract.false)
         Just ((_, ls, _), AST.Boolean False) -> literalSynthesis ((start, ls, end), Abstract.true)
         _ -> SynCFExp{folded= Mapped (pos, Abstract.not $ foldedExp' $ syn expr),
                       foldedValue= Nothing}
   synthesis _ (pos, AST.IsA _ right) _ (AST.IsA left _) =
      SynCFExp{folded= Mapped (pos, Abstract.is (foldedExp' $ syn left) right),
               foldedValue= Nothing}
   synthesis _ (pos, _) _ (AST.Set elements) =
      SynCFExp{folded= Mapped (pos, Abstract.set (getMapped . folded' . syn <$> getZipList elements)),
               foldedValue= Nothing}
   synthesis _ (pos, _) _ (AST.Read des) =
      case syn des :: SynCFDesignator l
      of SynCFDesignator{designatorValue= Just val} -> literalSynthesis val
         SynCFDesignator{folded= Mapped (pos', des'),
                         designatorValue= Nothing} -> SynCFExp{folded= Mapped (pos, Abstract.read (pos', des')),
                                                               foldedValue= Nothing}
   synthesis _ (pos, _) _ (AST.FunctionCall fn args) =
      case (snd <$> designatorValue (syn fn :: SynCFDesignator l), (snd <$>) . foldedValue . syn <$> getZipList args)
      of (Just (AST.Builtin "CAP"), [Just (AST.String s)])
            | Text.length s == 1, capital <- Text.toUpper s -> fromValue (Abstract.string capital)
         (Just (AST.Builtin "CAP"), [Just (AST.CharCode c)])
            | capital <- ord (toUpper $ chr c) -> fromValue (Abstract.charCode capital)
         (Just (AST.Builtin "CHR"), [Just (AST.Integer code)]) -> fromValue (Abstract.charCode $ fromIntegral code)
         (Just (AST.Builtin "ORD"), [Just (AST.String s)])
            | Text.length s == 1, code <- ord (Text.head s) -> fromValue (Abstract.integer $ toInteger code)
         (Just (AST.Builtin "ORD"), [Just (AST.CharCode code)]) -> fromValue (Abstract.integer $ toInteger code)
         (Just (AST.Builtin "ABS"), [Just (AST.Integer i)]) -> fromValue (Abstract.integer $ abs i)
         (Just (AST.Builtin "ABS"), [Just (AST.Real r)]) -> fromValue (Abstract.real $ abs r)
         (Just (AST.Builtin "ASH"), [Just (AST.Integer i), Just (AST.Integer j)])
            | shifted <- shift i (fromIntegral j) -> fromValue (Abstract.integer shifted)
         (Just (AST.Builtin "ENTIER"), [Just (AST.Real x)]) -> fromValue (Abstract.integer $ ceiling x)
         (Just (AST.Builtin "LEN"), [Just (AST.String s)]) -> fromValue (Abstract.integer
                                                                            $ toInteger $ Text.length s)
         (Just (AST.Builtin "LONG"), [Just (AST.Integer x)]) -> fromValue (Abstract.integer x)
         (Just (AST.Builtin "LONG"), [Just (AST.Real x)]) -> fromValue (Abstract.real x)
         (Just (AST.Builtin "SHORT"), [Just (AST.Integer x)]) -> fromValue (Abstract.integer x)
         (Just (AST.Builtin "SHORT"), [Just (AST.Real x)]) -> fromValue (Abstract.real x)
         (Just (AST.Builtin "ODD"), [Just (AST.Integer x)]) ->
            fromValue (if x `mod` 2 == 1 then Abstract.true else Abstract.false)
         (Just (AST.Builtin "SIZE"), [Just (AST.Builtin "INTEGER")]) -> fromValue (Abstract.integer intSize)
         (Just (AST.Builtin "SIZE"), [Just (AST.Builtin "LONGINT")]) -> fromValue (Abstract.integer intSize)
         (Just (AST.Builtin "SIZE"), [Just (AST.Builtin "SHORTINT")]) -> fromValue (Abstract.integer int32Size)
         (Just (AST.Builtin "SIZE"), [Just (AST.Builtin "REAL")]) -> fromValue (Abstract.integer doubleSize)
         (Just (AST.Builtin "SIZE"), [Just (AST.Builtin "LONGREAL")]) -> fromValue (Abstract.integer doubleSize)
         (Just (AST.Builtin "SIZE"), [Just (AST.Builtin "SHORTREAL")]) -> fromValue (Abstract.integer floatSize)
         (Just (AST.Builtin "MAX"), [Just (AST.Builtin "CHAR")]) -> fromValue (Abstract.charCode 0xff)
         (Just (AST.Builtin "MAX"), [Just (AST.Builtin "INTEGER")]) -> fromValue (Abstract.integer maxInteger)
         (Just (AST.Builtin "MAX"), [Just (AST.Builtin "LONGINT")]) -> fromValue (Abstract.integer maxInteger)
         (Just (AST.Builtin "MAX"), [Just (AST.Builtin "SHORTINT")]) -> fromValue (Abstract.integer maxInt32)
         (Just (AST.Builtin "MAX"), [Just (AST.Builtin "SET")]) -> fromValue (Abstract.integer maxSet)
         (Just (AST.Builtin "MAX"), [Just (AST.Builtin "REAL")]) -> fromValue (Abstract.real maxReal)
         (Just (AST.Builtin "MAX"), [Just (AST.Builtin "LONGREAL")]) -> fromValue (Abstract.real maxReal)
         (Just (AST.Builtin "MIN"), [Just (AST.Builtin "CHAR")]) -> fromValue (Abstract.charCode 0)
         (Just (AST.Builtin "MIN"), [Just (AST.Builtin "INTEGER")]) -> fromValue (Abstract.integer minInteger)
         (Just (AST.Builtin "MIN"), [Just (AST.Builtin "LONGINT")]) -> fromValue (Abstract.integer minInteger)
         (Just (AST.Builtin "MIN"), [Just (AST.Builtin "SHORTINT")]) -> fromValue (Abstract.integer minInt32)
         (Just (AST.Builtin "MIN"), [Just (AST.Builtin "SET")]) -> fromValue (Abstract.integer minSet)
         (Just (AST.Builtin "MIN"), [Just (AST.Builtin "REAL")]) -> fromValue (Abstract.real minReal)
         (Just (AST.Builtin "MIN"), [Just (AST.Builtin "LONGREAL")]) -> fromValue (Abstract.real minReal)
         _ -> SynCFExp{folded= Mapped (pos,
                                       Abstract.functionCall (getMapped $ folded (syn fn :: SynCFDesignator l))
                                                             (foldedExp' . syn <$> getZipList args)),
                       foldedValue= Nothing}
      where fromValue v = literalSynthesis (pos, v)
   synthesis _ (pos, _) _ (AST.Literal val) =
      SynCFExp{folded= Mapped (pos, Abstract.literal $ getMapped $ folded' $ syn val),
               foldedValue= Just (pos, snd $ getMapped $ folded' $ syn val)}

literalSynthesis :: (Abstract.Wirthy λ, Deep.Functor (Transformation.Rank2.Map Placed Identity) (Abstract.Value l l),
                     Pretty (Abstract.Value l l Identity Identity)) =>
                    Placed (Abstract.Value l l Placed Placed) -> SynCFExp λ l
literalSynthesis v@((start, Trailing l, end), value) =
   SynCFExp{folded= Mapped ((start, mempty, end),
                            Abstract.literal ((start, lexemes, end), value)),
            foldedValue= Just v}
   where lexemes = Trailing ([Token{lexemeType= Other,
                                    lexemeText= renderStrict $ layoutCompact $ pretty
                                                $ (Identity . snd) Transformation.Rank2.<$> value}]
                             <> filter isWhiteSpace l)
         isWhiteSpace WhiteSpace{} = True
         isWhiteSpace _ = False

maxInteger, minInteger, maxInt32, minInt32, maxSet, minSet :: Integer
maxInteger = toInteger (maxBound :: Int)
minInteger = toInteger (minBound :: Int)
maxInt32 = toInteger (maxBound :: Int32)
minInt32 = toInteger (minBound :: Int32)
maxSet = 63
minSet = 0

doubleSize, floatSize, intSize, int32Size :: Integer
doubleSize = toInteger (sizeOf (0 :: Double))
floatSize = toInteger (sizeOf (0 :: Float))
intSize = toInteger (sizeOf (0 :: Int))
int32Size = toInteger (sizeOf (0 :: Int32))

maxReal, minReal :: Double
maxReal = encodeFloat (floatRadix x - 1) (snd (floatRange x) - 1)
   where x = 0 :: Double
minReal = encodeFloat (floatRadix x - 1) (fst (floatRange x))
   where x = 0 :: Double

foldBinaryArithmetic :: forall λ l f. (f ~ Placed, Abstract.Value l ~ AST.Value l, Abstract.Wirthy λ,
                                  Pretty (Abstract.Value l l Identity Identity)) =>
                        (Int, ParsedLexemes, Int)
                     -> (f (Abstract.Expression l l f f) -> f (Abstract.Expression l l f f) -> Abstract.Expression λ l f f)
                     -> (forall n. Num n => n -> n -> n)
                     -> SynCFExp l l -> SynCFExp l l -> SynCFExp λ l
foldBinaryArithmetic pos@(start, _, end) node op l r =
   case join (foldValues <$> foldedValue l <*> foldedValue r)
   of Just v -> literalSynthesis v
      Nothing -> SynCFExp{folded= Mapped (pos, node (foldedExp' l) (foldedExp' r)),
                          foldedValue= Nothing}
   where foldValues :: Placed (AST.Value l l f f) -> Placed (AST.Value l l f f) -> Maybe (Placed (AST.Value l l f f))
         foldBareValues :: AST.Value l l f f -> AST.Value l l f f -> Maybe (AST.Value l l f f)
         foldValues (_, l') ((_, ls, _), r') = (,) (start, ls, end) <$> foldBareValues l' r'
         foldBareValues (AST.Integer l') (AST.Integer r') = Just (AST.Integer $ op l' r')
         foldBareValues (AST.Real l')    (AST.Real r')    = Just (AST.Real $ op l' r')
         foldBareValues (AST.Integer l') (AST.Real r')    = Just (AST.Real $ op (fromIntegral l') r')
         foldBareValues (AST.Real l')    (AST.Integer r') = Just (AST.Real $ op l' (fromIntegral r'))
         foldBareValues _ _ = Nothing

foldBinaryFractional :: forall λ l f. (f ~ Placed, Abstract.Value l ~ AST.Value l, Abstract.Wirthy λ,
                                  Pretty (Abstract.Value l l Identity Identity)) =>
                        (Int, ParsedLexemes, Int)
                     -> (f (Abstract.Expression l l f f) -> f (Abstract.Expression l l f f) -> Abstract.Expression λ l f f)
                     -> (forall n. Fractional n => n -> n -> n)
                     -> SynCFExp l l -> SynCFExp l l -> SynCFExp λ l
foldBinaryFractional pos@(start, _, end) node op l r =
   case join (foldValues <$> foldedValue l <*> foldedValue r)
   of Just v -> literalSynthesis v
      Nothing -> SynCFExp{folded= Mapped (pos, node (foldedExp' l) (foldedExp' r)),
                          foldedValue= Nothing}
   where foldValues :: Placed (AST.Value l l f f) -> Placed (AST.Value l l f f) -> Maybe (Placed (AST.Value l l f f))
         foldValues (_, AST.Real l') ((_, ls, _), AST.Real r') = Just ((start, ls, end), AST.Real $ op l' r')
         foldValues _ _ = Nothing

foldBinaryInteger :: forall λ l f. (f ~ Placed, Abstract.Value l ~ AST.Value l, Abstract.Wirthy λ,
                               Pretty (Abstract.Value l l Identity Identity)) =>
                        (Int, ParsedLexemes, Int)
                     -> (f (Abstract.Expression l l f f) -> f (Abstract.Expression l l f f) -> Abstract.Expression λ l f f)
                     -> (forall n. Integral n => n -> n -> n)
                     -> SynCFExp l l -> SynCFExp l l -> SynCFExp λ l
foldBinaryInteger pos@(start, _, end) node op l r =
   case join (foldValues <$> foldedValue l <*> foldedValue r)
   of Just v -> literalSynthesis v
      Nothing -> SynCFExp{folded= Mapped (pos, node (foldedExp' l) (foldedExp' r)),
                          foldedValue= Nothing}
   where foldValues :: Placed (AST.Value l l f f) -> Placed (AST.Value l l f f) -> Maybe (Placed (AST.Value l l f f))
         foldValues (_, AST.Integer l') ((_, ls, _), AST.Integer r') = Just ((start, ls, end), AST.Integer $ op l' r')
         foldValues _ _ = Nothing

foldBinaryBoolean :: forall λ l f. (f ~ Placed, Abstract.Value l ~ AST.Value l, Abstract.Wirthy λ,
                               Pretty (Abstract.Value l l Identity Identity)) =>
                     (Int, ParsedLexemes, Int)
                  -> (f (Abstract.Expression l l f f) -> f (Abstract.Expression l l f f) -> Abstract.Expression λ l f f)
                  -> (Bool -> Bool -> Bool)
                  -> SynCFExp l l -> SynCFExp l l -> SynCFExp λ l
foldBinaryBoolean pos@(start, _, end) node op l r =
   case join (foldValues <$> foldedValue l <*> foldedValue r)
   of Just v -> literalSynthesis v
      Nothing -> SynCFExp{folded= Mapped (pos, node (foldedExp' l) (foldedExp' r)),
                          foldedValue= Nothing}
   where foldValues :: Placed (AST.Value l l f f) -> Placed (AST.Value l l f f) -> Maybe (Placed (AST.Value l l f f))
         foldValues (_, AST.Boolean l') ((_, ls, _), AST.Boolean r') = Just ((start, ls, end), AST.Boolean $ op l' r')
         foldValues _ _ = Nothing

instance (Ord (Abstract.QualIdent l), v ~ Abstract.Value l l Placed Placed) =>
         SynthesizedField "designatorValue" (Maybe (Placed v)) (Auto ConstantFold) (AST.Designator l l) Sem Placed where
   synthesizedField _ _ (pos, AST.Variable q) inheritance _ = (,) pos <$> join (Map.lookup q $ env inheritance)
   synthesizedField _ _ _ _ _ = Nothing

instance {-# overlaps #-} Ord (Abstract.QualIdent l) => Transformation.At (Auto ConstantFold) (Modules l Sem Sem) where
   ($) = AG.applyDefault snd

--- * Shortcut

instance Full.Functor (Auto ConstantFold) (AST.Value l l) where
   Auto ConstantFold <$> (pos, val) = Rank2.Arrow sem
      where sem _inherited = Synthesized (SynCF $ Mapped (pos, val))

-- * Unsafe Rank2 AST instances

instance Rank2.Apply (AST.Module l l f') where
   AST.Module name1 imports1 body1 <*> ~(AST.Module _name _imports body2) =
      AST.Module name1 imports1 (Rank2.apply body1 body2)

predefined, predefined2 :: (Abstract.Wirthy l, Ord (Abstract.QualIdent l)) => Environment l
-- | The set of predefined types and procedures defined in the Oberon Language Report.
predefined = Map.fromList $ map (first Abstract.nonQualIdent) $
   [("TRUE", Just Abstract.true),
    ("FALSE", Just Abstract.false)]
   ++ map builtin ["BOOLEAN", "CHAR", "SHORTINT", "INTEGER", "LONGINT", "REAL", "LONGREAL", "SET",
                   "ABS", "ASH", "CAP", "LEN", "MAX", "MIN",
                   "ODD", "SIZE", "ORD", "CHR", "SHORT", "LONG", "ENTIER"]
   where builtin name = (name, Just $ Abstract.builtin name)
predefined2 = predefined

$(do l <- varT  <$> newName "l"
     mconcat <$> mapM (\g-> Transformation.Full.TH.deriveUpFunctor (conT ''Auto `appT` conT ''ConstantFold)
                            $ conT g `appT` l `appT` l)
        [''AST.Declaration, ''AST.Type, ''AST.FieldList,
         ''AST.ProcedureHeading, ''AST.FormalParameters, ''AST.FPSection,
         ''AST.Expression, ''AST.Element, ''AST.Designator,
         ''AST.Block, ''AST.StatementSequence, ''AST.Statement,
         ''AST.Case, ''AST.CaseLabels, ''AST.ConditionalBranch, ''AST.WithAlternative])

$(do let sem = [t|Semantics (Auto ConstantFold)|]
     let inst g = [d| instance Attribution (Auto ConstantFold) ($g l l) Sem Placed =>
                               Transformation.At (Auto ConstantFold) ($g l l $sem $sem)
                         where ($) = AG.applyDefault snd |]
     mconcat <$> mapM (inst . conT)
        [''AST.Module, ''AST.Block, ''AST.Declaration, ''AST.Type, ''AST.FieldList,
         ''AST.ProcedureHeading, ''AST.FormalParameters, ''AST.FPSection,
         ''AST.StatementSequence, ''AST.Statement,
         ''AST.Case, ''AST.CaseLabels, ''AST.ConditionalBranch, ''AST.WithAlternative,
         ''AST.Element, ''AST.Expression, ''AST.Designator])
