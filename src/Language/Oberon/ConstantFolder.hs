{-# LANGUAGE DeriveGeneric, DuplicateRecordFields, FlexibleContexts, FlexibleInstances,
             MultiParamTypeClasses, OverloadedStrings, RankNTypes, ScopedTypeVariables,
             TemplateHaskell, TypeApplications, TypeFamilies, UndecidableInstances #-}

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

import qualified Rank2
import qualified Transformation
import qualified Transformation.Deep as Deep
import qualified Transformation.Full as Full
import qualified Transformation.Full.TH
import qualified Transformation.Shallow as Shallow
import qualified Transformation.AG as AG
import Transformation.AG (Attribution(..), Atts, Inherited(..), Synthesized(..), Semantics)
import Transformation.AG.Generics (Auto(Auto), Bequether(..), Synthesizer(..), Revelation(..), Mapped(..))

import qualified Language.Oberon.Abstract as Abstract
import qualified Language.Oberon.AST as AST
import Language.Oberon.Grammar (ParsedLexemes(Trailing))

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
   where wrap = (,) (0, Trailing [])

type Placed = (,) (Int, ParsedLexemes)

type Environment l = Map (Abstract.QualIdent l) (Maybe (Abstract.Value l l Placed Placed))

newtype Modules l f' f = Modules {getModules :: Map AST.Ident (f (AST.Module l l f' f'))}

data ConstantFold = ConstantFold

type Sem = Semantics (Auto ConstantFold)

instance Transformation.Transformation (Auto ConstantFold) where
   type Domain (Auto ConstantFold) = Placed
   type Codomain (Auto ConstantFold) = Semantics (Auto ConstantFold)

instance Revelation (Auto ConstantFold) where
  reveal = const snd

data InhCFRoot l = InhCFRoot{rootEnv :: Environment l} deriving Generic

data InhCF l = InhCF{env           :: Environment l,
                     currentModule :: AST.Ident}
               deriving Generic

data SynCF a = SynCF{folded :: Mapped Placed a} deriving Generic

data SynCFMod l a = SynCFMod{moduleEnv :: Environment l,
                             folded    :: Mapped Placed a}

data SynCFExp λ l = SynCFExp{folded   :: Mapped Placed (Abstract.Expression λ l Placed Placed),
                             foldedValue :: Maybe (Abstract.Value l l Placed Placed)}

data SynCFDesignator l = SynCFDesignator{folded :: Mapped Placed (Abstract.Designator l l Placed Placed),
                                         designatorValue :: Maybe (AST.Value l l Placed Placed)}

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


-- Disambiguation
foldedExp  :: SynCFExp λ l -> Mapped Placed (Abstract.Expression λ l Placed Placed)
foldedExp' :: SynCFExp λ l -> Placed (Abstract.Expression λ l Placed Placed)
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
   synthesis _ (_, AST.Module moduleName imports _body) inheritance (AST.Module _ _ body) =
      SynCFMod{moduleEnv= exportedEnv,
               folded= Mapped ((0, Trailing []),
                               AST.Module moduleName imports $ getMapped
                               $ folded (syn body :: SynCFMod' l (Abstract.Block l l)))}
      where exportedEnv = Map.mapKeysMonotonic export newEnv
            newEnv = moduleEnv (syn body)
            export q
               | Just name <- Abstract.getNonQualIdentName q = Abstract.qualIdent moduleName name
               | otherwise = q

instance {-# overlaps #-} (Abstract.Nameable l, Ord (Abstract.QualIdent l),
                           Atts (Synthesized (Auto ConstantFold)) (Abstract.Declaration l l Sem Sem)
                           ~ SynCFMod' l (Abstract.Declaration l l),
                           Atts (Synthesized (Auto ConstantFold)) (Abstract.Type l l Sem Sem) ~ SynCF' (Abstract.Type l l),
                           Atts (Synthesized (Auto ConstantFold)) (Abstract.ProcedureHeading l l Sem Sem)
                           ~ SynCF' (Abstract.ProcedureHeading l l),
                           Atts (Synthesized (Auto ConstantFold)) (Abstract.FormalParameters l l Sem Sem)
                           ~ SynCF' (Abstract.FormalParameters l l),
                           Atts (Synthesized (Auto ConstantFold)) (Abstract.Block l l Sem Sem) ~ SynCFMod' l (Abstract.Block l l),
                           Atts (Synthesized (Auto ConstantFold)) (Abstract.ConstExpression l l Sem Sem) ~ SynCFExp l l) =>
                          Synthesizer (Auto ConstantFold) (AST.Declaration l l) Sem Placed where
   synthesis _ (pos, AST.ConstantDeclaration namedef _) _ (AST.ConstantDeclaration _ expression) =
      SynCFMod{moduleEnv= Map.singleton (Abstract.nonQualIdent name) val,
               folded = Mapped (pos,
                                AST.ConstantDeclaration namedef $
                                maybe (foldedExp' $ syn expression) ((,) pos . Abstract.literal . (,) pos) val)}
      where name = Abstract.getIdentDefName namedef
            val = foldedValue (syn expression)
   synthesis _ (pos, AST.TypeDeclaration namedef _) _ (AST.TypeDeclaration _ definition) =
      SynCFMod{moduleEnv= mempty,
               folded = Mapped (pos, AST.TypeDeclaration namedef
                                     $ getMapped $ folded (syn definition :: SynCF' (Abstract.Type l l)))}
   synthesis _ (pos, AST.VariableDeclaration names _declaredType) _
             (AST.VariableDeclaration _names declaredType) =
      SynCFMod{moduleEnv= mempty,
               folded= Mapped (pos, AST.VariableDeclaration names
                                    $ getMapped $ folded (syn declaredType :: SynCF' (Abstract.Type l l)))}
   synthesis _ (pos, _) _ (AST.ProcedureDeclaration heading body) =
      SynCFMod{moduleEnv= mempty,
               folded= Mapped (pos, AST.ProcedureDeclaration
                                       (getMapped $ folded (syn heading :: SynCF' (Abstract.ProcedureHeading l l)))
                                       (getMapped $ folded (syn body :: SynCFMod' l (Abstract.Block l l))))}
   synthesis _ (pos, AST.ForwardDeclaration namedef _signature) _
             (AST.ForwardDeclaration _namedef signature) =
      SynCFMod{moduleEnv= mempty,
               folded= Mapped (pos, AST.ForwardDeclaration namedef $ getMapped . foldedSignature . syn <$> signature)}
      where foldedSignature :: SynCF' (Abstract.FormalParameters l l)
                            -> Mapped Placed (Abstract.FormalParameters l l Placed Placed)
            foldedSignature = folded

instance {-# overlaps #-} (Abstract.Oberon l, Abstract.Nameable l, Ord (Abstract.QualIdent l), Show (Abstract.QualIdent l),
                           Atts (Synthesized (Auto ConstantFold)) (Abstract.Declaration l l Sem Sem)
                           ~ SynCFMod' l (Abstract.Declaration l l),
                           Atts (Synthesized (Auto ConstantFold)) (Abstract.StatementSequence l l Sem Sem)
                           ~ SynCF' (Abstract.StatementSequence l l)) =>
                          Synthesizer (Auto ConstantFold) (AST.Block l l) Sem Placed where
   synthesis _ (pos, AST.Block _decls _stats) inheritance (AST.Block decls stats) =
      SynCFMod{moduleEnv= Map.unions (moduleEnv . syn <$> decls),
               folded= Mapped (pos, AST.Block (getMapped . foldedDeclaration . syn <$> decls)
                                              (getMapped . foldedStatements . syn <$> stats))}
      where foldedDeclaration :: SynCFMod' l (Abstract.Declaration l l)
                              -> Mapped Placed (Abstract.Declaration l l Placed Placed)
            foldedDeclaration = folded
            foldedStatements :: SynCF' (Abstract.StatementSequence l l)
                             -> Mapped Placed (Abstract.StatementSequence l l Placed Placed)
            foldedStatements = folded

instance {-# overlaps #-} (Abstract.Oberon l, Abstract.Nameable l, Ord (Abstract.QualIdent l),
                           Abstract.Value l ~ AST.Value l, InhCF l ~ InhCF λ,
                           Atts (Synthesized (Auto ConstantFold)) (Abstract.Expression l l Sem Sem) ~ SynCFExp λ l,
                           Atts (Synthesized (Auto ConstantFold)) (Abstract.Element l l Sem Sem) ~ SynCF' (Abstract.Element l l),
                           Atts (Synthesized (Auto ConstantFold)) (Abstract.Designator l l Sem Sem) ~ SynCFDesignator l) =>
                          Synthesizer (Auto ConstantFold) (AST.Expression λ l) Sem Placed where
   synthesis _ (pos, AST.Relation op _ _) _ (AST.Relation _op left right) =
      case join (compareValues <$> foldedValue (syn left) <*> foldedValue (syn right))
      of Just value -> SynCFExp{folded= Mapped (pos, Abstract.literal (pos, value)),
                                foldedValue= Just value}
         Nothing -> SynCFExp{folded= Mapped (pos,
                                             Abstract.relation op (foldedExp' $ syn left) (foldedExp' $ syn right)),
                             foldedValue= Nothing}
      where compareValues (AST.Boolean l) (AST.Boolean r)   = relate op (compare l r)
            compareValues (AST.Integer l) (AST.Integer r)   = relate op (compare l r)
            compareValues (AST.Real l) (AST.Real r)         = relate op (compare l r)
            compareValues (AST.Integer l) (AST.Real r)      = relate op (compare (fromIntegral l) r)
            compareValues (AST.Real l) (AST.Integer r)      = relate op (compare l (fromIntegral r))
            compareValues (AST.CharCode l) (AST.CharCode r) = relate op (compare l r)
            compareValues (AST.String l) (AST.String r)     = relate op (compare l r)
            compareValues (AST.CharCode l) (AST.String r)   = relate op (compare (Text.singleton $ chr l) r)
            compareValues (AST.String l) (AST.CharCode r)   = relate op (compare l (Text.singleton $ chr r))
            compareValues _ _                               = Nothing
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
   synthesis _ (pos, _) _ (AST.Positive expr) =
      case foldedValue (syn expr)
      of Just (AST.Integer n) -> SynCFExp{folded= Mapped (pos, Abstract.literal (pos, AST.Integer n)),
                                          foldedValue= Just (AST.Integer n)}
         Just (AST.Real n) -> SynCFExp{folded= Mapped (pos, Abstract.literal (pos, AST.Real n)),
                                       foldedValue= Just (AST.Real n)}
         _ -> SynCFExp{folded= Mapped (pos, Abstract.positive $ foldedExp' $ syn expr),
                       foldedValue= Nothing}
   synthesis _ (pos, _) _ (AST.Negative expr) =
      case foldedValue (syn expr)
      of Just (AST.Integer n) -> SynCFExp{folded= Mapped (pos, Abstract.literal (pos, AST.Integer $ negate n)),
                                          foldedValue= Just (AST.Integer $ negate n)}
         Just (AST.Real n) -> SynCFExp{folded= Mapped (pos, Abstract.literal (pos, AST.Real $ negate n)),
                                       foldedValue= Just (AST.Real $ negate n)}
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
   synthesis _ (pos, _) _ (AST.Not expr) =
      case foldedValue (syn expr)
      of Just (AST.Boolean True) -> SynCFExp{folded= Mapped (pos, Abstract.literal (pos, Abstract.false)),
                                             foldedValue= Just Abstract.false}
         Just (AST.Boolean False) -> SynCFExp{folded= Mapped (pos, Abstract.literal (pos, Abstract.true)),
                                              foldedValue= Just Abstract.true}
         _ -> SynCFExp{folded= Mapped (pos, Abstract.not $ foldedExp' $ syn expr),
                       foldedValue= Nothing}
   synthesis _ (pos, AST.IsA _ right) _ (AST.IsA left _) =
      SynCFExp{folded= Mapped (pos, Abstract.is (foldedExp' $ syn left) right),
               foldedValue= Nothing}
   synthesis _ (pos, _) _ (AST.Set elements) =
      SynCFExp{folded= Mapped (pos, Abstract.set (getMapped . foldedElement . syn <$> getZipList elements)),
               foldedValue= Nothing}
      where foldedElement :: SynCF' (Abstract.Element l l) -> Mapped Placed (Abstract.Element l l Placed Placed)
            foldedElement = folded
   synthesis _ (pos, _) _ (AST.Read des) =
      case syn des :: SynCFDesignator l
      of SynCFDesignator{folded= Mapped (pos', _),
                         designatorValue= Just val} -> SynCFExp{folded= Mapped (pos, Abstract.literal (pos', val)),
                                                                foldedValue= Just val}
         SynCFDesignator{folded= Mapped (pos', des'),
                         designatorValue= Nothing} -> SynCFExp{folded= Mapped (pos, Abstract.read (pos', des')),
                                                               foldedValue= Nothing}
   synthesis _ (pos, _) _ (AST.FunctionCall fn args) =
      case (designatorValue (syn fn :: SynCFDesignator l), foldedValue . syn <$> getZipList args)
      of (Just (AST.Builtin "CAP"), [Just (AST.String s)])
            | Text.length s == 1, capital <- Text.toUpper s -> literalSynthesis (Abstract.string capital)
         (Just (AST.Builtin "CAP"), [Just (AST.CharCode c)])
            | capital <- ord (toUpper $ chr c) -> literalSynthesis (Abstract.charCode capital)
         (Just (AST.Builtin "CHR"), [Just (AST.Integer code)]) -> literalSynthesis (Abstract.charCode $ fromIntegral code)
         (Just (AST.Builtin "ORD"), [Just (AST.String s)])
            | Text.length s == 1, code <- ord (Text.head s) -> literalSynthesis (Abstract.integer $ toInteger code)
         (Just (AST.Builtin "ORD"), [Just (AST.CharCode code)]) -> literalSynthesis (Abstract.integer $ toInteger code)
         (Just (AST.Builtin "ABS"), [Just (AST.Integer i)]) -> literalSynthesis (Abstract.integer $ abs i)
         (Just (AST.Builtin "ABS"), [Just (AST.Real r)]) -> literalSynthesis (Abstract.real $ abs r)
         (Just (AST.Builtin "ASH"), [Just (AST.Integer i), Just (AST.Integer j)])
            | shifted <- shift i (fromIntegral j) -> literalSynthesis (Abstract.integer shifted)
         (Just (AST.Builtin "ENTIER"), [Just (AST.Real x)]) -> literalSynthesis (Abstract.integer $ ceiling x)
         (Just (AST.Builtin "LEN"), [Just (AST.String s)]) -> literalSynthesis (Abstract.integer $ toInteger $ Text.length s)
         (Just (AST.Builtin "LONG"), [Just (AST.Integer x)]) -> literalSynthesis (Abstract.integer x)
         (Just (AST.Builtin "LONG"), [Just (AST.Real x)]) -> literalSynthesis (Abstract.real x)
         (Just (AST.Builtin "SHORT"), [Just (AST.Integer x)]) -> literalSynthesis (Abstract.integer x)
         (Just (AST.Builtin "SHORT"), [Just (AST.Real x)]) -> literalSynthesis (Abstract.real x)
         (Just (AST.Builtin "ODD"), [Just (AST.Integer x)]) ->
            literalSynthesis (if x `mod` 2 == 1 then Abstract.true else Abstract.false)
         (Just (AST.Builtin "SIZE"), [Just (AST.Builtin "INTEGER")]) -> literalSynthesis (Abstract.integer intSize)
         (Just (AST.Builtin "SIZE"), [Just (AST.Builtin "LONGINT")]) -> literalSynthesis (Abstract.integer intSize)
         (Just (AST.Builtin "SIZE"), [Just (AST.Builtin "SHORTINT")]) -> literalSynthesis (Abstract.integer int32Size)
         (Just (AST.Builtin "SIZE"), [Just (AST.Builtin "REAL")]) -> literalSynthesis (Abstract.integer doubleSize)
         (Just (AST.Builtin "SIZE"), [Just (AST.Builtin "LONGREAL")]) -> literalSynthesis (Abstract.integer doubleSize)
         (Just (AST.Builtin "SIZE"), [Just (AST.Builtin "SHORTREAL")]) -> literalSynthesis (Abstract.integer floatSize)
         (Just (AST.Builtin "MAX"), [Just (AST.Builtin "CHAR")]) -> literalSynthesis (Abstract.charCode 0xff)
         (Just (AST.Builtin "MAX"), [Just (AST.Builtin "INTEGER")]) -> literalSynthesis (Abstract.integer maxInteger)
         (Just (AST.Builtin "MAX"), [Just (AST.Builtin "LONGINT")]) -> literalSynthesis (Abstract.integer maxInteger)
         (Just (AST.Builtin "MAX"), [Just (AST.Builtin "SHORTINT")]) -> literalSynthesis (Abstract.integer maxInt32)
         (Just (AST.Builtin "MAX"), [Just (AST.Builtin "SET")]) -> literalSynthesis (Abstract.integer maxSet)
         (Just (AST.Builtin "MAX"), [Just (AST.Builtin "REAL")]) -> literalSynthesis (Abstract.real maxReal)
         (Just (AST.Builtin "MAX"), [Just (AST.Builtin "LONGREAL")]) -> literalSynthesis (Abstract.real maxReal)
         (Just (AST.Builtin "MIN"), [Just (AST.Builtin "CHAR")]) -> literalSynthesis (Abstract.charCode 0)
         (Just (AST.Builtin "MIN"), [Just (AST.Builtin "INTEGER")]) -> literalSynthesis (Abstract.integer minInteger)
         (Just (AST.Builtin "MIN"), [Just (AST.Builtin "LONGINT")]) -> literalSynthesis (Abstract.integer minInteger)
         (Just (AST.Builtin "MIN"), [Just (AST.Builtin "SHORTINT")]) -> literalSynthesis (Abstract.integer minInt32)
         (Just (AST.Builtin "MIN"), [Just (AST.Builtin "SET")]) -> literalSynthesis (Abstract.integer minSet)
         (Just (AST.Builtin "MIN"), [Just (AST.Builtin "REAL")]) -> literalSynthesis (Abstract.real minReal)
         (Just (AST.Builtin "MIN"), [Just (AST.Builtin "LONGREAL")]) -> literalSynthesis (Abstract.real minReal)
         _ -> SynCFExp{folded= Mapped (pos,
                                       Abstract.functionCall (getMapped $ folded (syn fn :: SynCFDesignator l))
                                                             (foldedExp' . syn <$> getZipList args)),
                       foldedValue= Nothing}
      where literalSynthesis value = SynCFExp{folded= Mapped (pos, Abstract.literal (pos, value)),
                                              foldedValue= Just value}
   synthesis _ (pos, _) _ (AST.Literal val) =
      SynCFExp{folded= Mapped (pos, Abstract.literal $ getMapped $ folded (syn val :: SynCF' (AST.Value l l))),
               foldedValue= Just (snd $ getMapped $ folded (syn val :: SynCF' (AST.Value l l)))}

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

foldBinaryArithmetic :: forall λ l f. (f ~ Placed, Abstract.Value l ~ AST.Value l, Abstract.Wirthy λ) =>
                        (Int, ParsedLexemes)
                     -> (f (Abstract.Expression λ l f f) -> f (Abstract.Expression λ l f f) -> Abstract.Expression λ l f f)
                     -> (forall n. Num n => n -> n -> n)
                     -> SynCFExp λ l -> SynCFExp λ l -> SynCFExp λ l
foldBinaryArithmetic pos node op l r = case join (foldValues <$> foldedValue l <*> foldedValue r)
                                       of Just v -> SynCFExp{folded= Mapped (pos, Abstract.literal (pos, v)),
                                                             foldedValue= Just v}
                                          Nothing -> SynCFExp{folded= Mapped (pos, node (foldedExp' l) (foldedExp' r)),
                                                              foldedValue= Nothing}
   where foldValues :: AST.Value l l f f -> AST.Value l l f f -> Maybe (AST.Value l l f f)
         foldValues (AST.Integer l') (AST.Integer r') = Just (AST.Integer $ op l' r')
         foldValues (AST.Real l')    (AST.Real r')    = Just (AST.Real $ op l' r')
         foldValues (AST.Integer l') (AST.Real r')    = Just (AST.Real $ op (fromIntegral l') r')
         foldValues (AST.Real l')    (AST.Integer r') = Just (AST.Real $ op l' (fromIntegral r'))
         foldValues _ _ = Nothing

foldBinaryFractional :: forall λ l f. (f ~ Placed, Abstract.Value l ~ AST.Value l, Abstract.Wirthy λ) =>
                        (Int, ParsedLexemes)
                     -> (f (Abstract.Expression λ l f f) -> f (Abstract.Expression λ l f f) -> Abstract.Expression λ l f f)
                     -> (forall n. Fractional n => n -> n -> n)
                     -> SynCFExp λ l -> SynCFExp λ l -> SynCFExp λ l
foldBinaryFractional pos node op l r = case join (foldValues <$> foldedValue l <*> foldedValue r)
                                       of Just v -> SynCFExp{folded= Mapped (pos, Abstract.literal (pos, v)),
                                                             foldedValue= Just v}
                                          Nothing -> SynCFExp{folded= Mapped (pos, node (foldedExp' l) (foldedExp' r)),
                                                              foldedValue= Nothing}
   where foldValues :: AST.Value l l f f -> AST.Value l l f f -> Maybe (AST.Value l l f f)
         foldValues (AST.Real l')    (AST.Real r')    = Just (AST.Real $ op l' r')
         foldValues _ _ = Nothing

foldBinaryInteger :: forall λ l f. (f ~ Placed, Abstract.Value l ~ AST.Value l, Abstract.Wirthy λ) =>
                        (Int, ParsedLexemes)
                     -> (f (Abstract.Expression λ l f f) -> f (Abstract.Expression λ l f f) -> Abstract.Expression λ l f f)
                     -> (forall n. Integral n => n -> n -> n)
                     -> SynCFExp λ l -> SynCFExp λ l -> SynCFExp λ l
foldBinaryInteger pos node op l r = case join (foldValues <$> foldedValue l <*> foldedValue r)
                                    of Just v -> SynCFExp{folded= Mapped (pos, Abstract.literal (pos, v)),
                                                          foldedValue= Just v}
                                       Nothing -> SynCFExp{folded= Mapped (pos, node (foldedExp' l) (foldedExp' r)),
                                                           foldedValue= Nothing}
   where foldValues :: AST.Value l l f f -> AST.Value l l f f -> Maybe (AST.Value l l f f)
         foldValues (AST.Integer l') (AST.Integer r') = Just (AST.Integer $ op l' r')
         foldValues _ _ = Nothing

foldBinaryBoolean :: forall λ l f. (f ~ Placed, Abstract.Value l ~ AST.Value l, Abstract.Wirthy λ) =>
                     (Int, ParsedLexemes)
                  -> (f (Abstract.Expression λ l f f) -> f (Abstract.Expression λ l f f) -> Abstract.Expression λ l f f)
                  -> (Bool -> Bool -> Bool)
                  -> SynCFExp λ l -> SynCFExp λ l -> SynCFExp λ l
foldBinaryBoolean pos node op l r = case join (foldValues <$> foldedValue l <*> foldedValue r)
                                    of Just v -> SynCFExp{folded= Mapped (pos, Abstract.literal (pos, v)),
                                                          foldedValue= Just v}
                                       Nothing -> SynCFExp{folded= Mapped (pos, node (foldedExp' l) (foldedExp' r)),
                                                           foldedValue= Nothing}
   where foldValues :: AST.Value l l f f -> AST.Value l l f f -> Maybe (AST.Value l l f f)
         foldValues (AST.Boolean l') (AST.Boolean r') = Just (AST.Boolean $ op l' r')
         foldValues _ _ = Nothing

instance {-# overlaps #-} (Abstract.CoWirthy l, Abstract.Nameable l, Abstract.Oberon l, Ord (Abstract.QualIdent l),
                           Abstract.Designator l l Placed Placed ~ AST.Designator l l Placed Placed,
                           Abstract.Expression l l Placed Placed ~ AST.Expression l l Placed Placed,
                           Abstract.Value l l Placed Placed ~ AST.Value l l Placed Placed,
                           Atts (Inherited (Auto ConstantFold)) (Abstract.Expression l l Sem Sem) ~ InhCF l,
                           Atts (Inherited (Auto ConstantFold)) (Abstract.Designator l l Sem Sem) ~ InhCF l,
                           Atts (Synthesized (Auto ConstantFold)) (Abstract.Expression l l Sem Sem) ~ SynCFExp λ l,
                           Atts (Synthesized (Auto ConstantFold)) (Abstract.Designator l l Sem Sem)
                           ~ SynCFDesignator l) =>
                          Synthesizer (Auto ConstantFold) (AST.Designator l l) Sem Placed where
   synthesis _ (pos, AST.Variable q) inheritance _ =
      SynCFDesignator{folded= Mapped (pos, AST.Variable q),
                      designatorValue= join (Map.lookup q $ env inheritance)}
--                                         >>= Abstract.coExpression :: Maybe (AST.Expression l l Placed Placed)))}
   synthesis _ (pos, AST.Field _record fieldName) _ (AST.Field record _fieldName) =
      SynCFDesignator{folded= Mapped (pos, AST.Field (getMapped $ folded (syn record :: SynCFDesignator l)) fieldName),
                      designatorValue= Nothing}
   synthesis _ (pos, AST.Index{}) _ (AST.Index array index indexes) =
      SynCFDesignator{folded= Mapped (pos, AST.Index (getMapped $ folded (syn array :: SynCFDesignator l))
                                                         (getMapped $ foldedExp $ syn index)
                                                         (getMapped . foldedExp . syn <$> indexes)),
                      designatorValue= Nothing}
   synthesis _ (pos, AST.TypeGuard _designator q) _ (AST.TypeGuard designator _q) =
      SynCFDesignator{folded= Mapped (pos, AST.TypeGuard (getMapped $ folded (syn designator :: SynCFDesignator l)) q),
                      designatorValue= Nothing}
   synthesis _ (pos, _) _ (AST.Dereference pointer) =
      SynCFDesignator{folded= Mapped (pos, AST.Dereference $ getMapped $ folded (syn pointer :: SynCFDesignator l)),
                      designatorValue= Nothing}

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
-- | The set of 'Predefined' types and procedures defined in the Oberon Language Report.
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
