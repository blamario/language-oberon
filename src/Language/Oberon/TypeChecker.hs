{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, OverloadedStrings,
             ScopedTypeVariables, TemplateHaskell, TypeFamilies, TypeOperators, UndecidableInstances, ViewPatterns #-}

module Language.Oberon.TypeChecker (Error, errorMessage, checkModules, predefined, predefined2) where

import Control.Applicative (liftA2, (<|>), ZipList(ZipList, getZipList))
import Control.Arrow (first)
import Data.Coerce (coerce)
import qualified Data.List as List
import Data.Functor.Const (Const(..))
import Data.Maybe (fromMaybe)
import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as Map
import Data.Semigroup (Semigroup(..))
import qualified Data.Text as Text
import Language.Haskell.TH (appT, conT, varT, newName)

import qualified Rank2
import qualified Transformation
import qualified Transformation.Shallow as Shallow
import qualified Transformation.Deep as Deep
import qualified Transformation.Full as Full
import qualified Transformation.Full.TH
import qualified Transformation.AG as AG
import Transformation.AG (Attribution(..), Atts, Inherited(..), Synthesized(..), Semantics)

import qualified Language.Oberon.Abstract as Abstract
import qualified Language.Oberon.AST as AST
import Language.Oberon.Grammar (ParsedLexemes(Trailing))

data Type l = NominalType (Abstract.QualIdent l) (Maybe (Type l))
            | RecordType{ancestry :: [Abstract.QualIdent l],
                         recordFields :: Map AST.Ident (Type l)}
            | NilType
            | IntegerType Int
            | StringType Int
            | ArrayType [Int] (Type l)
            | PointerType (Type l)
            | ReceiverType (Type l)
            | ProcedureType Bool [(Bool, Type l)] (Maybe (Type l))
            | BuiltinType Text.Text
            | UnknownType

data ErrorType l = ArgumentCountMismatch Int Int
                 | ExtraDimensionalIndex Int Int
                 | IncomparableTypes (Type l) (Type l)
                 | IncompatibleTypes (Type l) (Type l)
                 | TooSmallArrayType Int Int
                 | OpenArrayVariable
                 | NonArrayType (Type l)
                 | NonBooleanType (Type l)
                 | NonFunctionType (Type l)
                 | NonIntegerType (Type l)
                 | NonNumericType (Type l)
                 | NonPointerType (Type l)
                 | NonProcedureType (Type l)
                 | NonRecordType (Type l)
                 | TypeMismatch (Type l) (Type l)
                 | UnequalTypes (Type l) (Type l)
                 | UnrealType (Type l)
                 | UnknownName (Abstract.QualIdent l)
                 | UnknownField AST.Ident (Type l)

type Error l = (AST.Ident, (Int, ParsedLexemes), ErrorType l)

instance Eq (Abstract.QualIdent l) => Eq (Type l) where
  NominalType q1 (Just t1) == t2@(NominalType q2 _) = q1 == q2 || t1 == t2
  t1@(NominalType q1 _) == NominalType q2 (Just t2) = q1 == q2 || t1 == t2
  NominalType q1 Nothing == NominalType q2 Nothing = q1 == q2
  ArrayType [] t1 == ArrayType [] t2 = t1 == t2
  ProcedureType _ p1 r1 == ProcedureType _ p2 r2 = r1 == r2 && p1 == p2
  StringType len1 == StringType len2 = len1 == len2
  NilType == NilType = True
  BuiltinType name1 == BuiltinType name2 = name1 == name2
  ReceiverType t1 == t2 = t1 == t2
  t1 == ReceiverType t2 = t1 == t2
  _ == _ = False

instance Show (Abstract.QualIdent l) => Show (Type l) where
  show (NominalType q t) = "Nominal " ++ show q ++ " (" ++ shows t ")"
  show (RecordType ancestry fields) = "RecordType " ++ show ancestry ++ show (fst <$> Map.toList fields)
  show (ArrayType dimensions itemType) = "ArrayType " ++ show dimensions ++ " (" ++ shows itemType ")"
  show (PointerType targetType) = "PointerType " ++ show targetType
  show (ProcedureType _ parameters result) = "ProcedureType (" ++ show parameters ++ "): " ++ show result
  show (ReceiverType t) = "ReceiverType " ++ show t
  show (IntegerType n) = "IntegerType " ++ show n
  show (StringType len) = "StringType " ++ show len
  show (BuiltinType name) = "BuiltinType " ++ show name
  show NilType = "NilType"
  show UnknownType = "UnknownType"

errorMessage :: (Abstract.Nameable l, Abstract.Oberon l, Show (Abstract.QualIdent l)) => ErrorType l -> String
errorMessage (ArgumentCountMismatch expected actual) =
   "Expected " <> show expected <> ", received " <> show actual <> " arguments"
errorMessage (ExtraDimensionalIndex expected actual) =
   "Expected " <> show expected <> ", received " <> show actual <> " indexes"
errorMessage (IncomparableTypes left right) = 
   "Values of types " <> typeMessage left <> " and " <> typeMessage right <> " cannot be compared"
errorMessage (IncompatibleTypes left right) =
   "Incompatible types " <> typeMessage left <> " and " <> typeMessage right
errorMessage (TooSmallArrayType expected actual) = 
   "The array of length " <> show expected <> " cannot contain " <> show actual <> " items"
errorMessage OpenArrayVariable = "A variable cannot be declared an open array"
errorMessage (NonArrayType t) = "Trying to index a non-array type " <> typeMessage t
errorMessage (NonBooleanType t) = "Type " <> typeMessage t <> " is not Boolean"
errorMessage (NonFunctionType t) = "Trying to invoke a " <> typeMessage t <> " as a function"
errorMessage (NonIntegerType t) = "Type " <> typeMessage t <> " is not an integer type"
errorMessage (NonNumericType t) = "Type " <> typeMessage t <> " is not a numeric type"
errorMessage (NonPointerType t) = "Trying to dereference a non-pointer type " <> typeMessage t
errorMessage (NonProcedureType t) = "Trying to invoke a " <> typeMessage t <> " as a procedure"
errorMessage (NonRecordType t) = "Non-record type " <> typeMessage t
errorMessage (TypeMismatch t1 t2) = "Type mismatch between " <> typeMessage t1 <> " and " <> typeMessage t2
errorMessage (UnequalTypes t1 t2) = "Unequal types " <> typeMessage t1 <> " and " <> typeMessage t2
errorMessage (UnrealType t) = "Type " <> typeMessage t <> " is not a numeric real type"
errorMessage (UnknownName q) = "Unknown name " <> show q
errorMessage (UnknownField name t) = "Record type " <> typeMessage t <> " has no field " <> show name

typeMessage :: (Abstract.Nameable l, Abstract.Oberon l) => Type l -> String
typeMessage (BuiltinType name) = Text.unpack name
typeMessage (NominalType name _) = nameMessage name
typeMessage (RecordType ancestry fields) = 
   "RECORD " ++ foldMap (("(" ++) . (++ ") ") . nameMessage) ancestry
   ++ List.intercalate ";\n" (fieldMessage <$> Map.toList fields) ++ "END"
   where fieldMessage (name, t) = "\n  " <> Text.unpack name <> ": " <> typeMessage t
typeMessage (ArrayType dimensions itemType) = 
   "ARRAY " ++ List.intercalate ", " (show <$> dimensions) ++ " OF " ++ typeMessage itemType
typeMessage (PointerType targetType) = "POINTER TO " ++ typeMessage targetType
typeMessage (ProcedureType _ parameters result) =
   "PROCEDURE (" ++ List.intercalate ", " (argMessage <$> parameters) ++ "): " ++ foldMap typeMessage result
   where argMessage (True, t) = "VAR " <> typeMessage t
         argMessage (False, t) = typeMessage t
typeMessage (ReceiverType t) = typeMessage t
typeMessage (IntegerType n) = "INTEGER"
typeMessage (StringType len) = "STRING [" ++ shows len "]"
typeMessage NilType = "NIL"
typeMessage UnknownType = "[Unknown]"

nameMessage :: (Abstract.Nameable l, Abstract.Oberon l) => Abstract.QualIdent l -> String
nameMessage q
   | Just (mod, name) <- Abstract.getQualIdentNames q = Text.unpack mod <> "." <> Text.unpack name
   | Just name <- Abstract.getNonQualIdentName q = Text.unpack name

type Environment l = Map (Abstract.QualIdent l) (Type l)

newtype Modules l f' f = Modules (Map AST.Ident (f (AST.Module l l f' f')))

data TypeCheck = TypeCheck

data TypeCheckErrors l = TypeCheckErrors

instance Transformation.Transformation (TypeCheckErrors l) where
   type Domain (TypeCheckErrors l) = Synthesized TypeCheck
   type Codomain (TypeCheckErrors l) = Const [Error l]

type Sem = Semantics TypeCheck

data InhTCRoot l = InhTCRoot{rootEnv :: Environment l}

data InhTC l = InhTC{env           :: Environment l,
                     currentModule :: AST.Ident}

data SynTC l = SynTC{errors :: [Error l]}

data SynTC' l = SynTC'{errors' :: [Error l],
                       env' :: Environment l}

data SynTCMod l = SynTCMod{moduleErrors :: [Error l],
                           moduleEnv :: Environment l,
                           pointerTargets :: Map AST.Ident AST.Ident}

data SynTCType l = SynTCType{typeErrors :: [Error l],
                             typeName   :: Maybe AST.Ident,
                             definedType :: Type l,
                             pointerTarget :: Maybe AST.Ident}

data SynTCFields l = SynTCFields{fieldErrors :: [Error l],
                                 fieldEnv :: Map AST.Ident (Type l)}

data SynTCHead l = SynTCHead{headingErrors :: [Error l],
                             insideEnv :: Environment l,
                             outsideEnv :: Environment l}

data SynTCSig l = SynTCSig{signatureErrors :: [Error l],
                           signatureEnv :: Environment l,
                           signatureType :: Type l}

data SynTCSec l = SynTCSec{sectionErrors :: [Error l],
                           sectionEnv :: Environment l,
                           sectionParameters :: [(Bool, Type l)]}

data SynTCDes l = SynTCDes{designatorErrors :: [Error l],
                           designatorName   :: Maybe (Maybe Abstract.Ident, Abstract.Ident),
                           designatorType :: Type l}

data SynTCExp l = SynTCExp{expressionErrors :: [Error l],
                           inferredType :: Type l}

-- * Modules instances, TH candidates
instance (Transformation.Transformation t, Functor (Transformation.Domain t), Deep.Functor t (AST.Module l l),
          Transformation.At t (AST.Module l l (Transformation.Codomain t) (Transformation.Codomain t))) =>
         Deep.Functor t (Modules l) where
   t <$> ~(Modules ms) = Modules (mapModule <$> ms)
      where mapModule m = t Transformation.$ ((t Deep.<$>) <$> m)

instance Transformation.At (TypeCheckErrors l) (AST.StatementSequence l l Sem Sem) where
   _ $ s = Const (errors $ syn s)
instance Transformation.At (TypeCheckErrors l) (AST.Statement l l Sem Sem) where
   _ $ s = Const (errors $ syn s)
instance Transformation.At (TypeCheckErrors l) (AST.ConditionalBranch l l Sem Sem) where
   _ $ s = Const (errors $ syn s)
instance Transformation.At (TypeCheckErrors l) (AST.Case l l Sem Sem) where
   _ $ s = Const (errors $ syn s)
instance Transformation.At (TypeCheckErrors l) (AST.WithAlternative l l Sem Sem) where
   _ $ s = Const (errors $ syn s)
instance Transformation.At (TypeCheckErrors l) (AST.Designator l l Sem Sem) where
   _ $ s = Const (designatorErrors $ syn s)
instance Transformation.At (TypeCheckErrors l) (AST.Expression l l Sem Sem) where
   _ $ s = Const (expressionErrors $ syn s)

instance Rank2.Functor (Modules l f') where
   f <$> ~(Modules ms) = Modules (f <$> ms)

instance Rank2.Apply (Modules l f') where
   ~(Modules fs) <*> ~(Modules ms) = Modules (Map.intersectionWith Rank2.apply fs ms)

-- * Boring attribute types
type instance Atts (Inherited TypeCheck) (Modules l _ _) = InhTCRoot l
type instance Atts (Synthesized TypeCheck) (Modules l _ _) = SynTC l
type instance Atts (Inherited TypeCheck) (AST.Module l l _ _) = InhTC l
type instance Atts (Synthesized TypeCheck) (AST.Module l l _ _) = SynTCMod l
type instance Atts (Inherited TypeCheck) (AST.Declaration l l _ _) = (InhTC l, Map AST.Ident AST.Ident)
type instance Atts (Synthesized TypeCheck) (AST.Declaration l l _ _) = SynTCMod l
type instance Atts (Inherited TypeCheck) (AST.ProcedureHeading l l _ _) = (InhTC l, Map AST.Ident AST.Ident)
type instance Atts (Synthesized TypeCheck) (AST.ProcedureHeading l l _ _) = SynTCHead l
type instance Atts (Inherited TypeCheck) (AST.Block l l _ _) = InhTC l
type instance Atts (Synthesized TypeCheck) (AST.Block l l _ _) = SynTCMod l
type instance Atts (Inherited TypeCheck) (AST.FormalParameters l l _ _) = InhTC l
type instance Atts (Synthesized TypeCheck) (AST.FormalParameters l l _ _) = SynTCSig l
type instance Atts (Inherited TypeCheck) (AST.FPSection l l _ _) = InhTC l
type instance Atts (Synthesized TypeCheck) (AST.FPSection l l _ _) = SynTCSec l
type instance Atts (Inherited TypeCheck) (AST.Type l l _ _) = InhTC l
type instance Atts (Synthesized TypeCheck) (AST.Type l l _ _) = SynTCType l
type instance Atts (Inherited TypeCheck) (AST.FieldList l l _ _) = InhTC l
type instance Atts (Synthesized TypeCheck) (AST.FieldList l l _ _) = SynTCFields l
type instance Atts (Inherited TypeCheck) (AST.StatementSequence l l _ _) = InhTC l
type instance Atts (Synthesized TypeCheck) (AST.StatementSequence l l _ _) = SynTC l
type instance Atts (Inherited TypeCheck) (AST.Expression l l _ _) = InhTC l
type instance Atts (Synthesized TypeCheck) (AST.Expression l l _ _) = SynTCExp l
type instance Atts (Inherited TypeCheck) (AST.Element l l _ _) = InhTC l
type instance Atts (Synthesized TypeCheck) (AST.Element l l _ _) = SynTCExp l
type instance Atts (Inherited TypeCheck) (AST.Value l l _ _) = InhTC l
type instance Atts (Synthesized TypeCheck) (AST.Value l l _ _) = SynTCExp l
type instance Atts (Inherited TypeCheck) (AST.Designator l l _ _) = InhTC l
type instance Atts (Synthesized TypeCheck) (AST.Designator l l _ _) = SynTCDes l
type instance Atts (Inherited TypeCheck) (AST.Statement l l _ _) = InhTC l
type instance Atts (Synthesized TypeCheck) (AST.Statement l l _ _) = SynTC l
type instance Atts (Inherited TypeCheck) (AST.ConditionalBranch l l _ _) = InhTC l
type instance Atts (Synthesized TypeCheck) (AST.ConditionalBranch l l _ _) = SynTC l
type instance Atts (Inherited TypeCheck) (AST.Case l l _ _) = (InhTC l, Type l)
type instance Atts (Synthesized TypeCheck) (AST.Case l l _ _) = SynTC l
type instance Atts (Inherited TypeCheck) (AST.CaseLabels l l _ _) = (InhTC l, Type l)
type instance Atts (Synthesized TypeCheck) (AST.CaseLabels l l _ _) = SynTC l
type instance Atts (Inherited TypeCheck) (AST.WithAlternative l l _ _) = InhTC l
type instance Atts (Synthesized TypeCheck) (AST.WithAlternative l l _ _) = SynTC l

-- * Rules

instance Ord (Abstract.QualIdent l) =>
         Attribution TypeCheck (Modules l) Sem Placed where
   attribution TypeCheck (_, Modules self) (Inherited inheritance, Modules ms) =
     (Synthesized SynTC{errors= foldMap (moduleErrors . syn) ms},
      Modules (Map.mapWithKey moduleInheritance self))
     where moduleInheritance name mod = Inherited InhTC{env= rootEnv inheritance <> foldMap (moduleEnv . syn) ms,
                                                        currentModule= name}

instance (Abstract.Oberon l, Abstract.Nameable l, Ord (Abstract.QualIdent l),
          Atts (Synthesized TypeCheck) (Abstract.Block l l Sem Sem) ~ SynTCMod l,
          Atts (Inherited TypeCheck) (Abstract.Block l l Sem Sem) ~ InhTC l) =>
         Attribution TypeCheck (AST.Module l l) Sem Placed where
   attribution TypeCheck (pos, AST.Module moduleName imports body) 
               (Inherited inheritance, AST.Module _ _ body') =
      (Synthesized SynTCMod{moduleErrors= moduleErrors (syn body'),
                            moduleEnv= exportedEnv,
                            pointerTargets= pointerTargets (syn body')},
       AST.Module moduleName imports (Inherited inheritance))
      where exportedEnv = exportNominal <$> Map.mapKeysMonotonic export (moduleEnv $ syn body')
            export q
               | Just name <- Abstract.getNonQualIdentName q = Abstract.qualIdent moduleName name
               | otherwise = q
            exportNominal (NominalType q (Just t))
               | Just name <- Abstract.getNonQualIdentName q =
                 NominalType (Abstract.qualIdent moduleName name) (Just $ exportNominal' t)
            exportNominal t = exportNominal' t
            exportNominal' (RecordType ancestry fields) = RecordType (export <$> ancestry) (exportNominal' <$> fields)
            exportNominal' (ProcedureType False parameters result) =
              ProcedureType False ((exportNominal' <$>) <$> parameters) (exportNominal' <$> result)
            exportNominal' (PointerType target) = PointerType (exportNominal' target)
            exportNominal' (ArrayType dimensions itemType) = ArrayType dimensions (exportNominal' itemType)
            exportNominal' (NominalType q (Just t))
              | Just name <- Abstract.getNonQualIdentName q =
                fromMaybe (NominalType (Abstract.qualIdent moduleName name) $ Just $ exportNominal' t)
                          (Map.lookup q exportedEnv)
            exportNominal' t = t

instance (Abstract.Nameable l, Ord (Abstract.QualIdent l),
          Atts (Inherited TypeCheck) (Abstract.Declaration l l Sem Sem) ~ (InhTC l, Map AST.Ident AST.Ident),
          Atts (Inherited TypeCheck) (Abstract.Type l l Sem Sem) ~ InhTC l,
          Atts (Inherited TypeCheck) (Abstract.ProcedureHeading l l Sem Sem) ~ (InhTC l, Map AST.Ident AST.Ident),
          Atts (Inherited TypeCheck) (Abstract.Block l l Sem Sem) ~ InhTC l,
          Atts (Inherited TypeCheck) (Abstract.FormalParameters l l Sem Sem) ~ InhTC l,
          Atts (Inherited TypeCheck) (Abstract.ConstExpression l l Sem Sem) ~ InhTC l,
          Atts (Synthesized TypeCheck) (Abstract.Declaration l l Sem Sem) ~ SynTCMod l,
          Atts (Synthesized TypeCheck) (Abstract.Type l l Sem Sem) ~ SynTCType l,
          Atts (Synthesized TypeCheck) (Abstract.FormalParameters l l Sem Sem) ~ SynTCSig l,
          Atts (Synthesized TypeCheck) (Abstract.ProcedureHeading l l Sem Sem) ~ SynTCHead l,
          Atts (Synthesized TypeCheck) (Abstract.Block l l Sem Sem) ~ SynTCMod l,
          Atts (Synthesized TypeCheck) (Abstract.ConstExpression l l Sem Sem) ~ SynTCExp l) =>
         Attribution TypeCheck (AST.Declaration l l) Sem Placed where
   attribution TypeCheck (pos, AST.ConstantDeclaration namedef _)
               (Inherited inheritance, AST.ConstantDeclaration _ expression) =
      (Synthesized SynTCMod{moduleErrors= expressionErrors (syn expression),
                            moduleEnv= Map.singleton (Abstract.nonQualIdent name) (inferredType $ syn expression),
                            pointerTargets= mempty},
       AST.ConstantDeclaration namedef (Inherited $ fst inheritance))
      where name = Abstract.getIdentDefName namedef
   attribution TypeCheck (pos, AST.TypeDeclaration namedef _)
               (Inherited inheritance, AST.TypeDeclaration _ definition) =
      (Synthesized SynTCMod{moduleErrors= typeErrors (syn definition),
                            moduleEnv= Map.singleton qname (nominal $ definedType $ syn definition),
                            pointerTargets= foldMap (Map.singleton name) (pointerTarget $ syn definition)},
       AST.TypeDeclaration namedef (Inherited $ fst inheritance))
      where nominal t@BuiltinType{} = t
            nominal t@NominalType{} = t
            nominal (PointerType t@RecordType{}) =
               NominalType qname (Just $ PointerType $ NominalType (Abstract.nonQualIdent $ name<>"^") (Just t))
            nominal t = NominalType qname (Just t)
            qname = Abstract.nonQualIdent name
            name = Abstract.getIdentDefName namedef
   attribution TypeCheck (pos, AST.VariableDeclaration names _declaredType)
               (Inherited inheritance, AST.VariableDeclaration _names declaredType) =
      (Synthesized SynTCMod{moduleErrors= typeErrors (syn declaredType) 
                                          <> case definedType (syn declaredType)
                                             of ArrayType [] _ -> [(currentModule $ fst inheritance, pos, OpenArrayVariable)]
                                                _ -> [],
                            moduleEnv= foldMap (\name-> Map.singleton (Abstract.nonQualIdent $ Abstract.getIdentDefName name)
                                                        (definedType $ syn declaredType))
                                       names,
                            pointerTargets= mempty},
       AST.VariableDeclaration names (Inherited $ fst inheritance))
   attribution TypeCheck (pos, AST.ProcedureDeclaration _heading _body)
               (Inherited inheritance, AST.ProcedureDeclaration heading body) =
      (Synthesized SynTCMod{moduleErrors= headingErrors (syn heading) <> moduleErrors (syn body),
                            moduleEnv= outsideEnv (syn heading),
                            pointerTargets= mempty},
       AST.ProcedureDeclaration (Inherited inheritance) (Inherited bodyInherited))
      where bodyInherited = InhTC (insideEnv (syn heading) `Map.union` env (fst inheritance))
                                  (currentModule $ fst inheritance)
   attribution TypeCheck (pos, AST.ForwardDeclaration namedef _signature)
               (Inherited inheritance, AST.ForwardDeclaration _namedef signature) =
      (Synthesized SynTCMod{moduleErrors= foldMap (signatureErrors . syn) signature,
                            moduleEnv= foldMap (Map.singleton (Abstract.nonQualIdent name) . signatureType . syn) signature,
                            pointerTargets= mempty},
       AST.ForwardDeclaration namedef (Just (Inherited $ fst inheritance)))
      where name = Abstract.getIdentDefName namedef

instance (Abstract.Nameable l, Ord (Abstract.QualIdent l),
          Atts (Inherited TypeCheck) (Abstract.FormalParameters l l Sem Sem) ~ InhTC l,
          Atts (Synthesized TypeCheck) (Abstract.FormalParameters l l Sem Sem) ~ SynTCSig l) =>
         Attribution TypeCheck (AST.ProcedureHeading l l) Sem Placed where
   attribution TypeCheck (pos, AST.ProcedureHeading indirect namedef _signature)
      (Inherited inheritance, AST.ProcedureHeading _indirect _ signature) =
      (Synthesized SynTCHead{headingErrors= foldMap (signatureErrors . syn) signature,
                             outsideEnv= Map.singleton (Abstract.nonQualIdent name) $
                                         maybe (ProcedureType False [] Nothing) (signatureType . syn) signature,
                             insideEnv= foldMap (signatureEnv . syn) signature},
       AST.ProcedureHeading indirect namedef (Just $ Inherited $ fst inheritance))
      where name = Abstract.getIdentDefName namedef
   attribution TypeCheck (pos, AST.TypeBoundHeading var receiverName receiverType indirect namedef _signature)
      (Inherited inheritance, AST.TypeBoundHeading _var _name _type _indirect _ signature) =
      (Synthesized SynTCHead{headingErrors= receiverError <> foldMap (signatureErrors . syn) signature,
                             outsideEnv=
                                case Map.lookup receiverType (snd inheritance)
                                  of Just targetName -> Map.singleton (Abstract.nonQualIdent targetName) methodType
                                     Nothing -> Map.singleton (Abstract.nonQualIdent receiverType) methodType,
                             insideEnv= receiverEnv `Map.union` foldMap (signatureEnv . syn) signature},
       AST.TypeBoundHeading var receiverName receiverType indirect namedef (Just $ Inherited $ fst inheritance))
      where receiverEnv =
               foldMap (Map.singleton (Abstract.nonQualIdent receiverName) . ReceiverType)
                       (Map.lookup (Abstract.nonQualIdent receiverType) $ env $ fst inheritance)
            methodType = NominalType (Abstract.nonQualIdent "") (Just $ RecordType [] $ Map.singleton name procedureType)
            name = Abstract.getIdentDefName namedef
            procedureType = maybe (ProcedureType False [] Nothing) (signatureType . syn) signature
            receiverError =
               case Map.lookup (Abstract.nonQualIdent receiverType) (env $ fst inheritance)
               of Nothing -> [(currentModule $ fst inheritance, pos, UnknownName $ Abstract.nonQualIdent receiverType)]
                  Just t 
                     | RecordType{} <- ultimate t -> []
                     | PointerType t' <- ultimate t, RecordType{} <- ultimate t' -> []
                     | otherwise -> [(currentModule $ fst inheritance, pos, NonRecordType t)]

instance (Abstract.Nameable l, Ord (Abstract.QualIdent l), Show (Abstract.QualIdent l),
          Atts (Inherited TypeCheck) (Abstract.Declaration l l Sem Sem) ~ (InhTC l, Map AST.Ident AST.Ident),
          Atts (Inherited TypeCheck) (Abstract.StatementSequence l l Sem Sem) ~ InhTC l,
          Atts (Synthesized TypeCheck) (Abstract.Declaration l l Sem Sem) ~ SynTCMod l,
          Atts (Synthesized TypeCheck) (Abstract.StatementSequence l l Sem Sem) ~ SynTC l) =>
         Attribution TypeCheck (AST.Block l l) Sem Placed where
   attribution TypeCheck (pos, AST.Block{}) (Inherited inheritance, AST.Block declarations statements) =
      (Synthesized SynTCMod{moduleErrors= foldMap (moduleErrors . syn) declarations
                                          <> foldMap (errors . syn) statements,
                            moduleEnv= newEnv,
                            pointerTargets= pointers},
       AST.Block (pure $ Inherited (localInherited, pointers)) (pure $ Inherited localInherited))
      where newEnv = Map.unionsWith mergeTypeBoundProcedures (moduleEnv . syn <$> declarations)
            localInherited = InhTC (newEnv <> env inheritance) (currentModule inheritance)
            pointers= foldMap (pointerTargets . syn) declarations
            mergeTypeBoundProcedures (NominalType q (Just t1)) t2
               | Abstract.getNonQualIdentName q == Just "" = mergeTypeBoundProcedures t1 t2
               | otherwise = NominalType q (Just $ mergeTypeBoundProcedures t1 t2)
            mergeTypeBoundProcedures t1 (NominalType q (Just t2))
               | Abstract.getNonQualIdentName q == Just "" = mergeTypeBoundProcedures t1 t2
               | otherwise = NominalType q (Just $ mergeTypeBoundProcedures t1 t2)
            mergeTypeBoundProcedures (RecordType ancestry1 fields1) (RecordType ancestry2 fields2) =
               RecordType (ancestry1 <> ancestry2) (fields1 <> fields2)
            mergeTypeBoundProcedures (PointerType (RecordType ancestry1 fields1)) (RecordType ancestry2 fields2) =
               PointerType (RecordType (ancestry1 <> ancestry2) (fields1 <> fields2))
            mergeTypeBoundProcedures (RecordType ancestry1 fields1) (PointerType (RecordType ancestry2 fields2)) =
               PointerType (RecordType (ancestry1 <> ancestry2) (fields1 <> fields2))
            mergeTypeBoundProcedures (PointerType (NominalType q (Just (RecordType ancestry1 fields1))))
                                     (RecordType ancestry2 fields2) =
               PointerType (NominalType q $ Just $ RecordType (ancestry1 <> ancestry2) (fields1 <> fields2))
            mergeTypeBoundProcedures (RecordType ancestry1 fields1)
                                     (PointerType (NominalType q (Just (RecordType ancestry2 fields2)))) =
               PointerType (NominalType q $ Just $ RecordType (ancestry1 <> ancestry2) (fields1 <> fields2))
            mergeTypeBoundProcedures t1 t2 = error (take 90 $ show t1)
            
instance (Ord (Abstract.QualIdent l),
          Atts (Inherited TypeCheck) (Abstract.FPSection l l Sem Sem) ~ InhTC l,
          Atts (Synthesized TypeCheck) (Abstract.FPSection l l Sem Sem) ~ SynTCSec l) =>
         Attribution TypeCheck (AST.FormalParameters l l) Sem Placed where
   attribution TypeCheck (pos, AST.FormalParameters sections returnType)
               (Inherited inheritance, AST.FormalParameters sections' _returnType) =
      (Synthesized SynTCSig{signatureErrors= foldMap (sectionErrors . syn) sections' <> foldMap typeRefErrors returnType,
                            signatureType= ProcedureType False (foldMap (sectionParameters . syn) sections')
                                           $ returnType >>= (`Map.lookup` env inheritance),
                            signatureEnv= foldMap (sectionEnv . syn) sections'},
       AST.FormalParameters (pure $ Inherited inheritance) returnType)
      where typeRefErrors q
               | Map.member q (env inheritance) = []
               | otherwise = [(currentModule inheritance, pos, UnknownName q)]

instance (Abstract.Wirthy l, Ord (Abstract.QualIdent l),
          Atts (Inherited TypeCheck) (Abstract.Type l l Sem Sem) ~ InhTC l,
          Atts (Synthesized TypeCheck) (Abstract.Type l l Sem Sem) ~ SynTCType l) =>
         Attribution TypeCheck (AST.FPSection l l) Sem Placed where
   attribution TypeCheck (pos, AST.FPSection var names _typeDef) (Inherited inheritance, AST.FPSection _var _names typeDef) =
      (Synthesized SynTCSec{sectionErrors= typeErrors (syn typeDef),
                            sectionParameters= (var, definedType (syn typeDef)) <$ names,
                            sectionEnv= Map.fromList (flip (,) (definedType $ syn typeDef) . Abstract.nonQualIdent
                                                      <$> names)},
       AST.FPSection var names (Inherited inheritance))

instance (Abstract.Nameable l, Ord (Abstract.QualIdent l),
          Atts (Inherited TypeCheck) (Abstract.FormalParameters l l Sem Sem) ~ InhTC l,
          Atts (Inherited TypeCheck) (Abstract.FieldList l l Sem Sem) ~ InhTC l,
          Atts (Inherited TypeCheck) (Abstract.Type l l Sem Sem) ~ InhTC l,
          Atts (Inherited TypeCheck) (Abstract.ConstExpression l l Sem Sem) ~ InhTC l,
          Atts (Synthesized TypeCheck) (Abstract.FormalParameters l l Sem Sem) ~ SynTCSig l,
          Atts (Synthesized TypeCheck) (Abstract.FieldList l l Sem Sem) ~ SynTCFields l,
          Atts (Synthesized TypeCheck) (Abstract.Type l l Sem Sem) ~ SynTCType l,
          Atts (Synthesized TypeCheck) (Abstract.ConstExpression l l Sem Sem) ~ SynTCExp l) =>
         Attribution TypeCheck (AST.Type l l) Sem Placed where
   attribution TypeCheck (pos, AST.TypeReference q) (Inherited inheritance, _) = 
      (Synthesized SynTCType{typeErrors= if Map.member q (env inheritance) then []
                                         else [(currentModule inheritance, pos, UnknownName q)],
                             typeName= Abstract.getNonQualIdentName q,
                             pointerTarget= Nothing,
                             definedType= fromMaybe UnknownType (Map.lookup q $ env inheritance)},
       AST.TypeReference q)
   attribution TypeCheck (pos, AST.ArrayType dimensions _itemType) (Inherited inheritance, AST.ArrayType dimensions' itemType) = 
      (Synthesized SynTCType{typeErrors= foldMap (expressionErrors . syn) dimensions' <> typeErrors (syn itemType)
                                         <> foldMap (expectInteger . syn) dimensions',
                             typeName= Nothing,
                             pointerTarget= Nothing,
                             definedType= ArrayType (integerValue . syn <$> getZipList dimensions')
                                                    (definedType $ syn itemType)},
       AST.ArrayType (ZipList [Inherited inheritance]) (Inherited inheritance))
     where expectInteger SynTCExp{inferredType= IntegerType{}} = []
           expectInteger SynTCExp{inferredType= t} = [(currentModule inheritance, pos, NonIntegerType t)]
           integerValue SynTCExp{inferredType= IntegerType n} = n
           integerValue _ = 0
   attribution TypeCheck (pos, AST.RecordType base fields) (Inherited inheritance, AST.RecordType _base fields') =
      (Synthesized SynTCType{typeErrors= fst baseRecord <> foldMap (fieldErrors . syn) fields',
                             typeName= Nothing,
                             pointerTarget= Nothing,
                             definedType= RecordType (maybe [] (maybe id (:) base . ancestry) $ snd baseRecord)
                                             (maybe Map.empty recordFields (snd baseRecord)
                                              <> foldMap (fieldEnv . syn) fields')},
       AST.RecordType base (pure $ Inherited inheritance))
     where baseRecord = case flip Map.lookup (env inheritance) <$> base
                        of Just (Just t@RecordType{}) -> ([], Just t)
                           Just (Just (NominalType _ (Just t@RecordType{}))) -> ([], Just t)
                           Just (Just t) -> ([(currentModule inheritance, pos, NonRecordType t)], Nothing)
                           Just Nothing -> (foldMap ((:[]) . (,,) (currentModule inheritance) pos . UnknownName) base,
                                            Nothing)
                           Nothing -> ([], Nothing)
   attribution TypeCheck _self (Inherited inheritance, AST.PointerType targetType') =
      (Synthesized SynTCType{typeErrors= typeErrors (syn targetType'),
                             typeName= Nothing,
                             pointerTarget= typeName (syn targetType'),
                             definedType= PointerType (definedType $ syn targetType')},
       AST.PointerType (Inherited inheritance))
   attribution TypeCheck (pos, AST.ProcedureType signature) (Inherited inheritance, AST.ProcedureType signature') = 
      (Synthesized SynTCType{typeErrors= foldMap (signatureErrors . syn) signature',
                             typeName= Nothing,
                             pointerTarget= Nothing,
                             definedType= maybe (ProcedureType False [] Nothing) (signatureType . syn) signature'},
       AST.ProcedureType (Inherited inheritance <$ signature))

instance (Abstract.Nameable l,
          Atts (Inherited TypeCheck) (Abstract.Type l l Sem Sem) ~ InhTC l,
          Atts (Synthesized TypeCheck) (Abstract.Type l l Sem Sem) ~ SynTCType l) =>
         Attribution TypeCheck (AST.FieldList l l) Sem Placed where
   attribution TypeCheck (pos, AST.FieldList names _declaredType) (Inherited inheritance, AST.FieldList _names declaredType) =
      (Synthesized SynTCFields{fieldErrors= typeErrors (syn declaredType),
                               fieldEnv= foldMap (\name-> Map.singleton (Abstract.getIdentDefName name)
                                                          (definedType $ syn declaredType)) 
                                         names},
       AST.FieldList names (Inherited inheritance))

instance (Atts (Inherited TypeCheck) (Abstract.Statement l l Sem Sem) ~ InhTC l,
          TypeCheckErrors l `Transformation.At` Abstract.Statement l l Sem Sem) =>
         Attribution TypeCheck (AST.StatementSequence l l) Sem Placed where
   bequest TypeCheck (_pos, statements) inheritance _ = AG.passDown (Inherited inheritance) statements
   synthesis TypeCheck _ _ statements = SynTC{errors= Shallow.foldMap TypeCheckErrors statements}

instance (Abstract.Wirthy l, Abstract.Nameable l, Ord (Abstract.QualIdent l),
          Atts (Inherited TypeCheck) (Abstract.StatementSequence l l Sem Sem) ~ InhTC l,
          Atts (Inherited TypeCheck) (Abstract.ConditionalBranch l l Sem Sem) ~ InhTC l,
          Atts (Inherited TypeCheck) (Abstract.Case l l Sem Sem) ~ (InhTC l, Type l),
          Atts (Inherited TypeCheck) (Abstract.WithAlternative l l Sem Sem) ~ InhTC l,
          Atts (Inherited TypeCheck) (Abstract.Expression l l Sem Sem) ~ InhTC l,
          Atts (Inherited TypeCheck) (Abstract.Designator l l Sem Sem) ~ InhTC l,
          Atts (Synthesized TypeCheck) (Abstract.StatementSequence l l Sem Sem) ~ SynTC l,
          Atts (Synthesized TypeCheck) (Abstract.Expression l l Sem Sem) ~ SynTCExp l,
          Atts (Synthesized TypeCheck) (Abstract.Designator l l Sem Sem) ~ SynTCDes l,
          TypeCheckErrors l `Transformation.At` Abstract.StatementSequence l l Sem Sem,
          TypeCheckErrors l `Transformation.At` Abstract.ConditionalBranch l l Sem Sem,
          TypeCheckErrors l `Transformation.At` Abstract.Case l l Sem Sem,
          TypeCheckErrors l `Transformation.At` Abstract.WithAlternative l l Sem Sem,
          TypeCheckErrors l `Transformation.At` Abstract.Designator l l Sem Sem,
          TypeCheckErrors l `Transformation.At` Abstract.Expression l l Sem Sem) =>
         Attribution TypeCheck (AST.Statement l l) Sem Placed where
   bequest TypeCheck (_pos, AST.EmptyStatement) i _   = AST.EmptyStatement
   bequest TypeCheck (_pos, AST.Assignment{}) i _     = AST.Assignment (AG.Inherited i) (AG.Inherited i)
   bequest TypeCheck (_pos, AST.ProcedureCall proc args) i _  =
      AST.ProcedureCall (AG.Inherited i) ((AG.Inherited i <$) <$> args)
   bequest TypeCheck (_pos, AST.If _branch branches _fallback) i _ =
      AST.If (AG.Inherited i) (AG.Inherited i <$ branches) (Just $ AG.Inherited i)
   bequest TypeCheck (_pos, AST.CaseStatement{}) i (AST.CaseStatement value _branches _fallback) =
      AST.CaseStatement (Inherited i) (pure $ Inherited (i, inferredType $ syn value)) (Just $ Inherited i)
   bequest TypeCheck (_pos, AST.While{}) i _          = AST.While (AG.Inherited i) (AG.Inherited i)
   bequest TypeCheck (_pos, AST.Repeat{}) i _         = AST.Repeat (AG.Inherited i) (AG.Inherited i)
   bequest TypeCheck (_pos, AST.For name _ _ _ _) i _ =
      AST.For name (AG.Inherited i) (AG.Inherited i) (pure $ AG.Inherited i) (AG.Inherited i)  -- Oberon2
   bequest TypeCheck (_pos, AST.Loop{}) i _           = AST.Loop (AG.Inherited i)
   bequest TypeCheck (_pos, AST.With{}) i _           =
      AST.With (AG.Inherited i) (pure $ AG.Inherited i) (Just $ AG.Inherited i)
   bequest TypeCheck (_pos, AST.Exit{}) i _           = AST.Exit
   bequest TypeCheck (_pos, AST.Return{}) i _         = AST.Return (Just $ AG.Inherited i)
   synthesis TypeCheck _ _ AST.EmptyStatement = SynTC{errors= []}
   synthesis TypeCheck (pos, _) inheritance statement@(AST.Assignment var value) = {-# SCC "Assignment" #-}
      SynTC{errors= assignmentCompatible inheritance pos (designatorType $ syn var) (inferredType $ syn value)
                    <> Shallow.foldMap TypeCheckErrors statement}
   synthesis TypeCheck (pos, AST.ProcedureCall _proc parameters)
             inheritance (AST.ProcedureCall procedure' parameters') =
      SynTC{errors= (case syn procedure'
                     of SynTCDes{designatorErrors= [],
                                 designatorType= t} -> procedureErrors t
                        SynTCDes{designatorErrors= errs} -> errs)
                    <> foldMap (foldMap (expressionErrors . syn)) parameters'}
     where procedureErrors (ProcedureType _ formalTypes Nothing)
             | length formalTypes /= maybe 0 (length . getZipList) parameters,
               not (length formalTypes == 2 && (length . getZipList <$> parameters) == Just 1
                    && designatorName (syn procedure') == Just (Nothing, "ASSERT")
                    || length formalTypes == 1 && (length . getZipList <$> parameters) == Just 2
                    && designatorName (syn procedure') == Just (Nothing, "NEW")
                    && all (all (isIntegerType . inferredType . syn) . tail . getZipList) parameters') =
                 [(currentModule inheritance, pos, ArgumentCountMismatch (length formalTypes)
                   $ maybe 0 (length . getZipList) parameters)]
             | otherwise = concat (zipWith (parameterCompatible inheritance pos) formalTypes
                                   $ maybe [] ((inferredType . syn <$>) . getZipList) parameters')
           procedureErrors (NominalType _ (Just t)) = procedureErrors t
           procedureErrors t = [(currentModule inheritance, pos, NonProcedureType t)]
   synthesis TypeCheck (pos, _) inheritance (AST.While condition body) =
      SynTC{errors= booleanExpressionErrors inheritance pos (syn condition) <> errors (syn body)}
   synthesis TypeCheck (pos, _) inheritance (AST.Repeat body condition) =
      SynTC{errors= booleanExpressionErrors inheritance pos (syn condition) <> errors (syn body)}
   synthesis TypeCheck (pos, _) inheritance (AST.For _counter start end step body) =
      SynTC{errors= integerExpressionErrors inheritance pos (syn start) 
                    <> integerExpressionErrors inheritance pos (syn end)
                    <> foldMap (integerExpressionErrors inheritance pos . syn) step <> errors (syn body)}
   synthesis TypeCheck self _ statement = SynTC{errors= Shallow.foldMap TypeCheckErrors statement}

instance (Abstract.Nameable l, Ord (Abstract.QualIdent l),
          Atts (Inherited TypeCheck) (Abstract.StatementSequence l l Sem Sem) ~ InhTC l,
          Atts (Synthesized TypeCheck) (Abstract.StatementSequence l l Sem Sem) ~ SynTC l) =>
         Attribution TypeCheck (AST.WithAlternative l l) Sem Placed where
   attribution TypeCheck (pos, AST.WithAlternative var subtype _body)
                         (Inherited inheritance, AST.WithAlternative _var _subtype body) =
      (Synthesized SynTC{errors= case (Map.lookup var (env inheritance),
                                       Map.lookup subtype (env inheritance))
                                 of (Just supertype, Just subtypeDef) -> assignmentCompatible inheritance pos supertype subtypeDef
                                    (Nothing, _) -> [(currentModule inheritance, pos, UnknownName var)]
                                    (_, Nothing) -> [(currentModule inheritance, pos, UnknownName subtype)]
                                 <> errors (syn body)},
       AST.WithAlternative var subtype (Inherited $ 
                                        InhTC (maybe id (Map.insert var) (Map.lookup subtype $ env inheritance) 
                                               $ env inheritance)
                                              (currentModule inheritance)))

instance (Abstract.Nameable l,
          Atts (Inherited TypeCheck) (Abstract.Expression l l Sem Sem) ~ InhTC l,
          Atts (Inherited TypeCheck) (Abstract.StatementSequence l l Sem Sem) ~ InhTC l,
          Atts (Synthesized TypeCheck) (Abstract.Expression l l Sem Sem) ~ SynTCExp l,
          Atts (Synthesized TypeCheck) (Abstract.StatementSequence l l Sem Sem) ~ SynTC l) =>
         Attribution TypeCheck (AST.ConditionalBranch l l) Sem Placed where
   attribution TypeCheck (pos, _) (Inherited inheritance, AST.ConditionalBranch condition body) =
      (Synthesized SynTC{errors= booleanExpressionErrors inheritance pos (syn condition) <> errors (syn body)},
       AST.ConditionalBranch (Inherited inheritance) (Inherited inheritance))

instance (Atts (Inherited TypeCheck) (Abstract.CaseLabels l l Sem Sem) ~ (InhTC l, Type l),
          Atts (Inherited TypeCheck) (Abstract.StatementSequence l l Sem Sem) ~ InhTC l,
          Atts (Synthesized TypeCheck) (Abstract.CaseLabels l l Sem Sem) ~ SynTC l,
          Atts (Synthesized TypeCheck) (Abstract.StatementSequence l l Sem Sem) ~ SynTC l) =>
         Attribution TypeCheck (AST.Case l l) Sem Placed where
   attribution TypeCheck self (Inherited inheritance, AST.Case label labels body) =
      (Synthesized SynTC{errors= errors (syn label) <> foldMap (errors . syn) labels <> errors (syn body)},
       AST.Case (Inherited inheritance) (pure $ Inherited inheritance) (Inherited $ fst inheritance))

instance forall l. (Abstract.Nameable l, Eq (Abstract.QualIdent l),
                    Atts (Inherited TypeCheck) (Abstract.ConstExpression l l Sem Sem) ~ InhTC l,
                    Atts (Synthesized TypeCheck) (Abstract.ConstExpression l l Sem Sem) ~ SynTCExp l) =>
         Attribution TypeCheck (AST.CaseLabels l l) Sem Placed where
   bequest TypeCheck (_, c) (inheritance, _) _ =
      (Inherited inheritance :: Inherited TypeCheck (Abstract.ConstExpression l l Sem Sem)) Shallow.<$> c
   synthesis TypeCheck (pos, _) inheritance (AST.SingleLabel value) =
      SynTC{errors= assignmentCompatible (fst inheritance) pos (snd inheritance) (inferredType $ syn value)}
   synthesis TypeCheck (pos, _) (inheritance, caseType) (AST.LabelRange start end) =
      SynTC{errors= assignmentCompatible inheritance pos caseType (inferredType $ syn start)
            <> assignmentCompatible inheritance pos caseType (inferredType $ syn end)}

instance (Abstract.Nameable l, Ord (Abstract.QualIdent l),
          Atts (Inherited TypeCheck) (Abstract.Expression l l Sem Sem) ~ InhTC l,
          Atts (Inherited TypeCheck) (Abstract.Element l l Sem Sem) ~ InhTC l,
          Atts (Inherited TypeCheck) (Abstract.Designator l l Sem Sem) ~ InhTC l,
          Atts (Inherited TypeCheck) (Abstract.Value l l Sem Sem) ~ InhTC l,
          Atts (Synthesized TypeCheck) (Abstract.Expression l l Sem Sem) ~ SynTCExp l,
          Atts (Synthesized TypeCheck) (Abstract.Element l l Sem Sem) ~ SynTCExp l,
          Atts (Synthesized TypeCheck) (Abstract.Value l l Sem Sem) ~ SynTCExp l,
          Atts (Synthesized TypeCheck) (Abstract.Designator l l Sem Sem) ~ SynTCDes l) =>
         Attribution TypeCheck (AST.Expression l l) Sem Placed where
   bequest TypeCheck (pos, e) inheritance _ = AG.passDown (Inherited inheritance) e
   synthesis TypeCheck (pos, AST.Relation op _ _) inheritance (AST.Relation _op left right) =
      SynTCExp{expressionErrors= case expressionErrors (syn left) <> expressionErrors (syn right)
                                 of [] | t1 == t2 -> []
                                       | AST.In <- op -> membershipCompatible (ultimate t1) (ultimate t2)
                                       | equality op, [] <- assignmentCompatible inheritance pos t1 t2 -> []
                                       | equality op, [] <- assignmentCompatible inheritance pos t2 t1 -> []
                                       | otherwise -> comparable (ultimate t1) (ultimate t2)
                                    errs -> errs,
               inferredType= BuiltinType "BOOLEAN"}
      where t1 = inferredType (syn left)
            t2 = inferredType (syn right)
            equality AST.Equal = True
            equality AST.Unequal = True
            equality _ = False
            comparable (BuiltinType "BOOLEAN") (BuiltinType "BOOLEAN") = []
            comparable (BuiltinType "CHAR") (BuiltinType "CHAR") = []
            comparable StringType{} StringType{} = []
            comparable (StringType 1) (BuiltinType "CHAR") = []
            comparable (BuiltinType "CHAR") (StringType 1) = []
            comparable StringType{} (ArrayType _ (BuiltinType "CHAR")) = []
            comparable (ArrayType _ (BuiltinType "CHAR")) StringType{} = []
            comparable (ArrayType _ (BuiltinType "CHAR")) (ArrayType _ (BuiltinType "CHAR")) = []
            comparable (BuiltinType t1) (BuiltinType t2)
               | isNumerical t1 && isNumerical t2 = []
            comparable (BuiltinType t1) IntegerType{}
               | isNumerical t1 = []
            comparable IntegerType{} (BuiltinType t2)
               | isNumerical t2 = []
            comparable t1 t2 = [(currentModule inheritance, pos, IncomparableTypes t1 t2)]
            membershipCompatible IntegerType{} (BuiltinType "SET") = []
            membershipCompatible (BuiltinType t1) (BuiltinType "SET")
               | isNumerical t1 = []
   synthesis TypeCheck (pos, AST.IsA _ q) inheritance (AST.IsA left _) =
      SynTCExp{expressionErrors= case Map.lookup q (env inheritance)
                                 of Nothing -> [(currentModule inheritance, pos, UnknownName q)]
                                    Just t -> assignmentCompatible inheritance pos (inferredType $ syn left) t,
               inferredType= BuiltinType "BOOLEAN"}
   synthesis TypeCheck (pos, _) inheritance (AST.Positive expr) =
      SynTCExp{expressionErrors= unaryNumericOrSetOperatorErrors inheritance pos (syn expr),
               inferredType= inferredType (syn expr)}
   synthesis TypeCheck (pos, _) inheritance (AST.Negative expr) =
      SynTCExp{expressionErrors= unaryNumericOrSetOperatorErrors inheritance pos (syn expr),
               inferredType= unaryNumericOrSetOperatorType negate (syn expr)}
   synthesis TypeCheck (pos, _) inheritance (AST.Add left right) =
      binaryNumericOrSetSynthesis inheritance pos left right
   synthesis TypeCheck (pos, _) inheritance (AST.Subtract left right) =
      binaryNumericOrSetSynthesis inheritance pos left right
   synthesis TypeCheck (pos, _) inheritance (AST.Or left right) = binaryBooleanSynthesis inheritance pos left right
   synthesis TypeCheck (pos, _) inheritance (AST.Multiply left right) =
      binaryNumericOrSetSynthesis inheritance pos left right
   synthesis TypeCheck (pos, _) inheritance (AST.Divide left right) =
      SynTCExp{expressionErrors=
                  case (syn left, syn right)
                  of (SynTCExp{expressionErrors= [], inferredType= BuiltinType t1},
                      SynTCExp{expressionErrors= [], inferredType= BuiltinType t2})
                        | t1 == "REAL", t2 == "REAL" -> []
                        | t1 == "SET", t2 == "SET" -> []
                     (SynTCExp{expressionErrors= [], inferredType= t1},
                      SynTCExp{expressionErrors= [], inferredType= t2})
                       | t1 == t2 -> [(currentModule inheritance, pos, UnrealType t1)]
                       | otherwise -> [(currentModule inheritance, pos, TypeMismatch t1 t2)],
               inferredType= BuiltinType "REAL"}
   synthesis TypeCheck (pos, _) inheritance (AST.IntegerDivide left right) =
      binaryIntegerSynthesis inheritance pos left right
   synthesis TypeCheck (pos, _) inheritance (AST.Modulo left right) = binaryIntegerSynthesis inheritance pos left right
   synthesis TypeCheck (pos, _) inheritance (AST.And left right) = binaryBooleanSynthesis inheritance pos left right
   synthesis TypeCheck _self _ (AST.Set elements) =
      SynTCExp{expressionErrors= mempty,
               inferredType= BuiltinType "SET"}
   synthesis TypeCheck _self _ (AST.Read designator) =
      SynTCExp{expressionErrors= designatorErrors (syn designator),
               inferredType= designatorType (syn designator)}
   synthesis TypeCheck _self _ (AST.Literal value) =
      SynTCExp{expressionErrors= expressionErrors (syn value),
               inferredType= inferredType (syn value)}
   synthesis TypeCheck (pos, AST.FunctionCall _designator (ZipList parameters)) inheritance
             (AST.FunctionCall designator (ZipList parameters')) =
      SynTCExp{expressionErrors=
                   case {-# SCC "FunctionCall" #-} syn designator
                   of SynTCDes{designatorErrors= [],
                               designatorName= name,
                               designatorType= ultimate -> ProcedureType _ formalTypes Just{}}
                        | length formalTypes /= length parameters ->
                            [(currentModule inheritance, pos,
                              ArgumentCountMismatch (length formalTypes)
                                                    (length parameters))]
                        | name == Just (Just "SYSTEM", "VAL") -> []
                        | otherwise -> concat (zipWith (parameterCompatible inheritance pos) formalTypes
                                               $ inferredType . syn <$> parameters')
                      SynTCDes{designatorErrors= [],
                               designatorType= t} -> [(currentModule inheritance, pos, NonFunctionType t)]
                      SynTCDes{designatorErrors= errs} -> errs
                   <> foldMap (expressionErrors . syn) parameters',
               inferredType=
                   case syn designator
                   of SynTCDes{designatorName= Just (Just "SYSTEM", name)}
                        | Just t <- systemCallType name (inferredType . syn <$> parameters') -> t
                      SynTCDes{designatorName= d, designatorType= t}
                        | ProcedureType _ _ (Just returnType) <- ultimate t -> returnType
                      _ -> UnknownType}
     where systemCallType "VAL" [t1, t2] = Just t1
           systemCallType _ _ = Nothing
   synthesis TypeCheck (pos, _) inheritance (AST.Not expr) =
      SynTCExp{expressionErrors= booleanExpressionErrors inheritance pos (syn expr),
               inferredType= BuiltinType "BOOLEAN"}

instance (Abstract.Wirthy l) => Attribution TypeCheck (AST.Value l l) Sem Placed where
   bequest TypeCheck (pos, val) inheritance _ = coerce val
   synthesis TypeCheck (pos, AST.Integer x) _ _ =
      SynTCExp{expressionErrors= mempty, inferredType= IntegerType $ fromIntegral x}
   synthesis TypeCheck (pos, AST.Real x) _ _ =
      SynTCExp{expressionErrors= mempty, inferredType= BuiltinType "REAL"}
   synthesis TypeCheck (pos, AST.Boolean x) _ _ =
      SynTCExp{expressionErrors= mempty, inferredType= BuiltinType "BOOLEAN"}
   synthesis TypeCheck (pos, AST.CharCode x) _ _ =
      SynTCExp{expressionErrors= mempty, inferredType= BuiltinType "CHAR"}
   synthesis TypeCheck (pos, AST.String x) _ _ =
      SynTCExp{expressionErrors= mempty, inferredType= StringType (Text.length x)}
   synthesis TypeCheck (pos, AST.Nil) _ _ = SynTCExp{expressionErrors= mempty, inferredType= NilType}
   synthesis TypeCheck (pos, AST.Builtin x) _ _ = SynTCExp{expressionErrors= mempty, inferredType= BuiltinType x}

instance (Abstract.Wirthy l, Abstract.Nameable l,
          Atts (Inherited TypeCheck) (Abstract.Expression l l Sem Sem) ~ InhTC l,
          Atts (Synthesized TypeCheck) (Abstract.Expression l l Sem Sem) ~ SynTCExp l) =>
         Attribution TypeCheck (AST.Element l l) Sem Placed where
   bequest TypeCheck (pos, elem) inheritance _ = AG.passDown (Inherited inheritance) elem
   synthesis TypeCheck (pos, _) inheritance (AST.Element expr) =
      SynTCExp{expressionErrors= integerExpressionErrors inheritance pos (syn expr),
               inferredType= BuiltinType "SET"}
   synthesis TypeCheck (pos, _) inheritance (AST.Range low high) =
      SynTCExp{expressionErrors= integerExpressionErrors inheritance pos (syn low)
                                 <> integerExpressionErrors inheritance pos (syn high),
               inferredType= BuiltinType "SET"}

instance (Abstract.Nameable l, Abstract.Oberon l, Ord (Abstract.QualIdent l), Show (Abstract.QualIdent l),
          Atts (Inherited TypeCheck) (Abstract.Expression l l Sem Sem) ~ InhTC l,
          Atts (Inherited TypeCheck) (Abstract.Designator l l Sem Sem) ~ InhTC l,
          Atts (Synthesized TypeCheck) (Abstract.Expression l l Sem Sem) ~ SynTCExp l,
          Atts (Synthesized TypeCheck) (Abstract.Designator l l Sem Sem) ~ SynTCDes l) =>
         Attribution TypeCheck (AST.Designator l l) Sem Placed where
   bequest TypeCheck (pos, d) inheritance _ = AG.passDown (Inherited inheritance) d
   synthesis TypeCheck (pos, AST.Variable q) inheritance _ =
      SynTCDes{designatorErrors= case designatorType
                                 of Nothing -> [(currentModule inheritance, pos, UnknownName q)]
                                    Just{} -> [],
               designatorName= (,) Nothing <$> Abstract.getNonQualIdentName q
                               <|> first Just <$> Abstract.getQualIdentNames q,
               designatorType= fromMaybe UnknownType designatorType}
      where designatorType = Map.lookup q (env inheritance)
   synthesis TypeCheck (pos, AST.Field _record fieldName) inheritance (AST.Field record _fieldName) =
      SynTCDes{designatorErrors= case syn record
                                 of SynTCDes{designatorErrors= [],
                                             designatorType= t} ->
                                      maybe [(currentModule inheritance, pos, NonRecordType t)]
                                            (maybe [(currentModule inheritance, pos, UnknownField fieldName t)] $ const [])
                                            (access True t)
                                    SynTCDes{designatorErrors= errors} -> errors,
               designatorName= Nothing,
               designatorType= fromMaybe UnknownType (fromMaybe Nothing $ access True
                                                      $ designatorType $ syn record)}
     where access _ (RecordType _ fields) = Just (Map.lookup fieldName fields)
           access True (PointerType t) = access False t
           access allowPtr (NominalType _ (Just t)) = access allowPtr t
           access allowPtr (ReceiverType t) = (receive <$>) <$> access allowPtr t
           access _ _ = Nothing
           receive (ProcedureType _ params result) = ProcedureType True params result
           receive t = t
   synthesis TypeCheck (pos, AST.Index _array index indexes) inheritance (AST.Index array _index _indexes) =
      SynTCDes{designatorErrors= case syn array
                                 of SynTCDes{designatorErrors= [],
                                             designatorType= t} ->
                                      either id (const []) (access True t)
                                    SynTCDes{designatorErrors= errors} -> errors,
               designatorType= either (const UnknownType) id (access True $ designatorType $ syn array)}
      where access _ (ArrayType dimensions t)
              | length dimensions == length indexes + 1 = Right t
              | length dimensions == 0 && length indexes == 0 = Right t
              | otherwise = Left [(currentModule inheritance, pos,
                                   ExtraDimensionalIndex (length dimensions) (1 + length indexes))]
            access allowPtr (NominalType _ (Just t)) = access allowPtr t
            access allowPtr (ReceiverType t) = access allowPtr t
            access True (PointerType t) = access False t
            access _ t = Left [(currentModule inheritance, pos, NonArrayType t)]
   synthesis TypeCheck (pos, AST.TypeGuard _designator q) inheritance (AST.TypeGuard designator _q) =
      SynTCDes{designatorErrors= case (syn designator, targetType)
                                 of (SynTCDes{designatorErrors= [],
                                              designatorType= t}, 
                                     Just t') -> assignmentCompatible inheritance pos t t'
                                    (SynTCDes{designatorErrors= errors}, 
                                     Nothing) -> (currentModule inheritance, pos, UnknownName q) : errors
                                    (SynTCDes{designatorErrors= errors}, _) -> errors,
               designatorType= fromMaybe UnknownType targetType}
      where targetType = Map.lookup q (env inheritance)
   synthesis TypeCheck (pos, _) inheritance (AST.Dereference pointer) =
      SynTCDes{designatorErrors= case syn pointer
                                 of SynTCDes{designatorErrors= [],
                                             designatorType= PointerType{}} -> []
                                    SynTCDes{designatorErrors= [],
                                             designatorType= NominalType _ (Just PointerType{})} -> []
                                    SynTCDes{designatorErrors= [],
                                             designatorType= ProcedureType True _ _} -> []
                                    SynTCDes{designatorErrors= [],
                                             designatorType= t} -> [(currentModule inheritance, pos, NonPointerType t)]
                                    SynTCDes{designatorErrors= errors} -> errors,
               designatorType= case designatorType (syn pointer)
                               of NominalType _ (Just (PointerType t)) -> t
                                  ProcedureType True params result -> ProcedureType False params result
                                  PointerType t -> t
                                  _ -> UnknownType}

binaryNumericOrSetSynthesis inheritance pos left right =
   SynTCExp{expressionErrors= binarySetOrNumericOperatorErrors inheritance pos (syn left) (syn right),
            inferredType= binaryNumericOperatorType (syn left) (syn right)}

binaryIntegerSynthesis inheritance pos left right =
   SynTCExp{expressionErrors= binaryIntegerOperatorErrors inheritance pos (syn left) (syn right),
            inferredType= binaryNumericOperatorType (syn left) (syn right)}

binaryBooleanSynthesis inheritance pos left right =
   SynTCExp{expressionErrors= binaryBooleanOperatorErrors inheritance pos (syn left) (syn right),
            inferredType= BuiltinType "BOOLEAN"}

unaryNumericOrSetOperatorErrors :: Abstract.Nameable l => InhTC l -> (Int, ParsedLexemes) -> SynTCExp l -> [Error l]
unaryNumericOrSetOperatorErrors _ _ SynTCExp{expressionErrors= [], inferredType= IntegerType{}} = []
unaryNumericOrSetOperatorErrors _ _ SynTCExp{expressionErrors= [],
                                             inferredType= BuiltinType name}
  | isNumerical name = []
  | name == "SET" = []
unaryNumericOrSetOperatorErrors inheritance pos SynTCExp{expressionErrors= [], inferredType= t} = 
   [(currentModule inheritance, pos, NonNumericType t)]
unaryNumericOrSetOperatorErrors _ _ SynTCExp{expressionErrors= errs} = errs

unaryNumericOrSetOperatorType :: (Int -> Int) -> SynTCExp l -> Type l
unaryNumericOrSetOperatorType f SynTCExp{inferredType= IntegerType x} = IntegerType (f x)
unaryNumericOrSetOperatorType _ SynTCExp{inferredType= t} = t

binarySetOrNumericOperatorErrors :: (Abstract.Nameable l, Eq (Abstract.QualIdent l))
                                 => InhTC l -> (Int, ParsedLexemes) -> SynTCExp l -> SynTCExp l -> [Error l]
binarySetOrNumericOperatorErrors _ _
  SynTCExp{expressionErrors= [], inferredType= BuiltinType name1}
  SynTCExp{expressionErrors= [], inferredType= BuiltinType name2}
  | isNumerical name1 && isNumerical name2 || name1 == "SET" && name2 == "SET" = []
binarySetOrNumericOperatorErrors _ _
  SynTCExp{expressionErrors= [], inferredType= IntegerType{}}
  SynTCExp{expressionErrors= [], inferredType= BuiltinType name}
  | isNumerical name = []
binarySetOrNumericOperatorErrors _ _
  SynTCExp{expressionErrors= [], inferredType= BuiltinType name}
  SynTCExp{expressionErrors= [], inferredType= IntegerType{}}
  | isNumerical name = []
binarySetOrNumericOperatorErrors _ _
  SynTCExp{expressionErrors= [], inferredType= IntegerType{}}
  SynTCExp{expressionErrors= [], inferredType= IntegerType{}} = []
binarySetOrNumericOperatorErrors inheritance pos SynTCExp{expressionErrors= [], inferredType= t1}
                                 SynTCExp{expressionErrors= [], inferredType= t2}
  | t1 == t2 = [(currentModule inheritance, pos, NonNumericType t1)]
  | otherwise = [(currentModule inheritance, pos, TypeMismatch t1 t2)]
binarySetOrNumericOperatorErrors _ _ SynTCExp{expressionErrors= errs1} SynTCExp{expressionErrors= errs2} = errs1 <> errs2

binaryNumericOperatorType :: (Abstract.Nameable l, Eq (Abstract.QualIdent l)) => SynTCExp l -> SynTCExp l -> Type l
binaryNumericOperatorType SynTCExp{inferredType= t1} SynTCExp{inferredType= t2}
  | t1 == t2 = t1
  | IntegerType{} <- t1 = t2
  | IntegerType{} <- t2 = t1
  | BuiltinType name1 <- t1, BuiltinType name2 <- t2,
    Just index1 <- List.elemIndex name1 numericTypeNames,
    Just index2 <- List.elemIndex name2 numericTypeNames = BuiltinType (numericTypeNames !! max index1 index2)
  | otherwise = t1

binaryIntegerOperatorErrors :: Abstract.Nameable l =>
                               InhTC l -> (Int, ParsedLexemes) ->  SynTCExp l -> SynTCExp l -> [Error l]
binaryIntegerOperatorErrors inheritance pos syn1 syn2 = integerExpressionErrors inheritance pos syn1 
                                                      <> integerExpressionErrors inheritance pos syn2

integerExpressionErrors inheritance pos SynTCExp{expressionErrors= [], inferredType= t}
  | isIntegerType t = []
  | otherwise = [(currentModule inheritance, pos, NonIntegerType t)]
integerExpressionErrors _ _ SynTCExp{expressionErrors= errs} = errs

isIntegerType IntegerType{} = True
isIntegerType (BuiltinType "SHORTINT") = True
isIntegerType (BuiltinType "INTEGER") = True
isIntegerType (BuiltinType "LONGINT") = True
isIntegerType t = False

booleanExpressionErrors _ _ SynTCExp{expressionErrors= [],
                                     inferredType= BuiltinType "BOOLEAN"} = []
booleanExpressionErrors inheritance pos SynTCExp{expressionErrors= [], inferredType= t} = 
   [(currentModule inheritance, pos, NonBooleanType t)]
booleanExpressionErrors _ _ SynTCExp{expressionErrors= errs} = errs

binaryBooleanOperatorErrors :: (Abstract.Nameable l, Eq (Abstract.QualIdent l))
                            => InhTC l -> (Int, ParsedLexemes) -> SynTCExp l -> SynTCExp l -> [Error l]
binaryBooleanOperatorErrors _inh _pos
  SynTCExp{expressionErrors= [], inferredType= BuiltinType "BOOLEAN"}
  SynTCExp{expressionErrors= [], inferredType= BuiltinType "BOOLEAN"} = []
binaryBooleanOperatorErrors inheritance pos
  SynTCExp{expressionErrors= [], inferredType= t1}
  SynTCExp{expressionErrors= [], inferredType= t2}
  | t1 == t2 = [(currentModule inheritance, pos, NonBooleanType t1)]
  | otherwise = [(currentModule inheritance, pos, TypeMismatch t1 t2)]
binaryBooleanOperatorErrors _ _ SynTCExp{expressionErrors= errs1} SynTCExp{expressionErrors= errs2} = errs1 <> errs2

parameterCompatible :: (Abstract.Nameable l, Eq (Abstract.QualIdent l))
                    => InhTC l -> (Int, ParsedLexemes) -> (Bool, Type l) -> Type l -> [Error l]
parameterCompatible _ _ (_, expected@(ArrayType [] _)) actual
  | arrayCompatible expected actual = []
parameterCompatible inheritance pos (True, expected) actual
  | expected == actual = []
  | otherwise = [(currentModule inheritance, pos, UnequalTypes expected actual)]
parameterCompatible inheritance pos (False, expected) actual
  | BuiltinType "ARRAY" <- expected, ArrayType{} <- actual = []
  | otherwise = assignmentCompatible inheritance pos expected actual

assignmentCompatible :: (Abstract.Nameable l, Eq (Abstract.QualIdent l))
                     => InhTC l -> (Int, ParsedLexemes) -> Type l -> Type l -> [Error l]
assignmentCompatible inheritance pos expected actual
   | expected == actual = []
   | BuiltinType name1 <- expected, BuiltinType name2 <- actual,
     Just index1 <- List.elemIndex name1 numericTypeNames,
     Just index2 <- List.elemIndex name2 numericTypeNames, 
     index1 >= index2 = []
   | BuiltinType name <- expected, IntegerType{} <- actual, isNumerical name = []
   | BuiltinType "BASIC TYPE" <- expected, BuiltinType name <- actual,
     name `elem` ["BOOLEAN", "CHAR", "SHORTINT", "INTEGER", "LONGINT", "REAL", "LONGREAL", "SET"] = []
   | BuiltinType "POINTER" <- expected, PointerType{} <- actual = []
   | BuiltinType "POINTER" <- expected, NominalType _ (Just t) <- actual =
       assignmentCompatible inheritance pos expected t
   | BuiltinType "CHAR" <- expected, actual == StringType 1 = []
   | ReceiverType t <- actual = assignmentCompatible inheritance pos expected t
   | ReceiverType t <- expected = assignmentCompatible inheritance pos t actual
   | NilType <- actual, PointerType{} <- expected = []
   | NilType <- actual, ProcedureType{} <- expected = []
   | NilType <- actual, NominalType _ (Just t) <- expected = assignmentCompatible inheritance pos t actual
--   | ArrayType [] (BuiltinType "CHAR") <- expected, StringType{} <- actual = []
   | ArrayType [m] (BuiltinType "CHAR") <- expected, StringType n <- actual =
      if m < n then [(currentModule inheritance, pos, TooSmallArrayType m n)] else []
   | targetExtends actual expected = []
   | NominalType _ (Just t) <- expected, ProcedureType{} <- actual = assignmentCompatible inheritance pos t actual
   | otherwise = [(currentModule inheritance, pos, IncompatibleTypes expected actual)]

arrayCompatible (ArrayType [] t1) (ArrayType _ t2) = t1 == t2 || arrayCompatible t1 t2
arrayCompatible (ArrayType [] (BuiltinType "CHAR")) StringType{} = True
arrayCompatible (NominalType _ (Just t1)) t2 = arrayCompatible t1 t2
arrayCompatible t1 (NominalType _ (Just t2)) = arrayCompatible t1 t2
arrayCompatible _ _ = False

extends, targetExtends :: Eq (Abstract.QualIdent l) => Type l -> Type l -> Bool
t1 `extends` t2 | t1 == t2 = True
RecordType ancestry _ `extends` NominalType q _ = q `elem` ancestry
NominalType _ (Just t1) `extends` t2 = t1 `extends` t2
t1 `extends` t2 = False -- error (show (t1, t2))

ultimate :: Type l -> Type l
ultimate (NominalType _ (Just t)) = ultimate t
ultimate t = t

isNumerical t = t `elem` numericTypeNames
numericTypeNames = ["SHORTINT", "INTEGER", "LONGINT", "REAL", "LONGREAL"]

PointerType t1 `targetExtends` PointerType t2 = t1 `extends` t2
NominalType _ (Just t1) `targetExtends` t2 = t1 `targetExtends` t2
t1 `targetExtends` NominalType _ (Just t2) = t1 `targetExtends` t2
t1 `targetExtends` t2 | t1 == t2 = True
t1 `targetExtends` t2 = False

instance Transformation.Transformation TypeCheck where
   type Domain TypeCheck = Placed
   type Codomain TypeCheck = Semantics TypeCheck

instance Ord (Abstract.QualIdent l) => Transformation.At TypeCheck (Modules l Sem Sem) where
   ($) = AG.applyDefault snd

-- * Unsafe Rank2 AST instances

instance Rank2.Apply (AST.Module l l f') where
   AST.Module name1 imports1 body1 <*> ~(AST.Module name2 imports2 body2) =
      AST.Module name1 imports1 (Rank2.apply body1 body2)

type Placed = (,) (Int, ParsedLexemes)

checkModules :: (Abstract.Oberon l, Abstract.Nameable l,
                 Ord (Abstract.QualIdent l), Show (Abstract.QualIdent l),
                 Atts (Inherited TypeCheck) (Abstract.Block l l Sem Sem) ~ InhTC l,
                 Atts (Synthesized TypeCheck) (Abstract.Block l l Sem Sem) ~ SynTCMod l,
                 Full.Functor TypeCheck (Abstract.Block l l))
             => Environment l -> Map AST.Ident (Placed (AST.Module l l Placed Placed)) -> [Error l]
checkModules predef modules =
   errors (syn (Transformation.apply TypeCheck (wrap $ TypeCheck Deep.<$> Modules modules)
                `Rank2.apply`
                Inherited (InhTCRoot predef)))
   where wrap = (,) (0, Trailing [])

predefined, predefined2 :: (Abstract.Wirthy l, Ord (Abstract.QualIdent l)) => Environment l
-- | The set of 'Predefined' types and procedures defined in the Oberon Language Report.
predefined = Map.fromList $ map (first Abstract.nonQualIdent) $
   [("BOOLEAN", BuiltinType "BOOLEAN"),
    ("CHAR", BuiltinType "CHAR"),
    ("SHORTINT", BuiltinType "SHORTINT"),
    ("INTEGER", BuiltinType "INTEGER"),
    ("LONGINT", BuiltinType "LONGINT"),
    ("REAL", BuiltinType "REAL"),
    ("LONGREAL", BuiltinType "LONGREAL"),
    ("SET", BuiltinType "SET"),
    ("TRUE", BuiltinType "BOOLEAN"),
    ("FALSE", BuiltinType "BOOLEAN"),
    ("ABS", ProcedureType False [(False, BuiltinType "INTEGER")] $ Just $ BuiltinType "INTEGER"),
    ("ASH", ProcedureType False [(False, BuiltinType "INTEGER")] $ Just $ BuiltinType "INTEGER"),
    ("CAP", ProcedureType False [(False, BuiltinType "CHAR")] $ Just $ BuiltinType "CHAR"),
    ("LEN", ProcedureType False [(False, BuiltinType "ARRAY")] $ Just $ BuiltinType "LONGINT"),
    ("MAX", ProcedureType False [(False, BuiltinType "BASIC TYPE")] $ Just UnknownType),
    ("MIN", ProcedureType False [(False, BuiltinType "BASIC TYPE")] $ Just UnknownType),
    ("ODD", ProcedureType False [(False, BuiltinType "CHAR")] $ Just $ BuiltinType "BOOLEAN"),
    ("SIZE", ProcedureType False [(False, BuiltinType "CHAR")] $ Just $ BuiltinType "INTEGER"),
    ("ORD", ProcedureType False [(False, BuiltinType "CHAR")] $ Just $ BuiltinType "INTEGER"),
    ("CHR", ProcedureType False [(False, BuiltinType "LONGINT")] $ Just $ BuiltinType "CHAR"),
    ("SHORT", ProcedureType False [(False, BuiltinType "LONGINT")] $ Just $ BuiltinType "SHORTINT"),
    ("LONG", ProcedureType False [(False, BuiltinType "INTEGER")] $ Just $ BuiltinType "INTEGER"),
    ("ENTIER", ProcedureType False [(False, BuiltinType "REAL")] $ Just $ BuiltinType "INTEGER"),
    ("INC", ProcedureType False [(False, BuiltinType "LONGINT")] Nothing),
    ("DEC", ProcedureType False [(False, BuiltinType "LONGINT")] Nothing),
    ("INCL", ProcedureType False [(False, BuiltinType "SET"), (False, BuiltinType "INTEGER")] Nothing),
    ("EXCL", ProcedureType False [(False, BuiltinType "SET"), (False, BuiltinType "INTEGER")] Nothing),
    ("COPY", ProcedureType False [(False, BuiltinType "ARRAY"), (False, BuiltinType "ARRAY")] Nothing),
    ("NEW", ProcedureType False [(False, BuiltinType "POINTER")] Nothing),
    ("HALT", ProcedureType False [(False, BuiltinType "INTEGER")] Nothing)]

-- | The set of 'Predefined' types and procedures defined in the Oberon-2 Language Report.
predefined2 = predefined <>
   Map.fromList (first Abstract.nonQualIdent <$>
                 [("ASSERT", ProcedureType False [(False, BuiltinType "BOOLEAN"),
                                                  (False, BuiltinType "INTEGER")] Nothing)])

$(do l <- varT <$> newName "l"
     mconcat <$> mapM (\t-> Transformation.Full.TH.deriveUpFunctor (conT ''TypeCheck) $ conT t `appT` l `appT` l)
        [''AST.Declaration, ''AST.Type, ''AST.FieldList,
         ''AST.ProcedureHeading, ''AST.FormalParameters, ''AST.FPSection,
         ''AST.Expression, ''AST.Element, ''AST.Designator,
         ''AST.Block, ''AST.StatementSequence, ''AST.Statement,
         ''AST.Case, ''AST.CaseLabels, ''AST.ConditionalBranch, ''AST.Value, ''AST.WithAlternative])

$(do let sem = [t|Semantics TypeCheck|]
     let inst g = [d| instance Attribution TypeCheck ($g l l) Sem Placed =>
                               Transformation.At TypeCheck ($g l l $sem $sem)
                         where ($) = AG.applyDefault snd |]
     mconcat <$> mapM (inst . conT)
        [''AST.Module, ''AST.Declaration, ''AST.Type, ''AST.FieldList,
         ''AST.ProcedureHeading, ''AST.FormalParameters, ''AST.FPSection,
         ''AST.Block, ''AST.StatementSequence, ''AST.Statement,
         ''AST.Case, ''AST.CaseLabels, ''AST.ConditionalBranch, ''AST.WithAlternative,
         ''AST.Expression, ''AST.Element, ''AST.Designator, ''AST.Value])
