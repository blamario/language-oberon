{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, OverloadedStrings,
             TemplateHaskell, TypeFamilies, UndecidableInstances #-}

module Language.Oberon.TypeChecker (Error, errorMessage, checkModules, predefined, predefined2) where

import Control.Applicative (liftA2, (<|>))
import Control.Arrow (first)
import qualified Data.List as List
import Data.Maybe (fromMaybe)
import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as Map
import Data.Semigroup (Semigroup(..))
import qualified Data.Text as Text
import Language.Haskell.TH (appT, conT, varT, newName)

import qualified Rank2
import qualified Transformation as Shallow
import qualified Transformation.Deep as Deep
import qualified Transformation.Full as Full
import qualified Transformation.Full.TH
import qualified Transformation.AG as AG
import Transformation.AG (Attribution(..), Atts, Inherited(..), Synthesized(..), Semantics)

import qualified Language.Oberon.Abstract as Abstract
import qualified Language.Oberon.AST as AST

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

type Error l = (AST.Ident, Int, ErrorType l)

instance Eq (Abstract.QualIdent l) => Eq (Type l) where
  NominalType q1 (Just t1) == t2@(NominalType q2 _) = q1 == q2 || t1 == t2
  t1@(NominalType q1 _) == NominalType q2 (Just t2) = q1 == q2 || t1 == t2
  NominalType q1 Nothing == NominalType q2 Nothing = q1 == q2
  ArrayType [] t1 == ArrayType [] t2 = t1 == t2
  ProcedureType _ p1 r1 == ProcedureType _ p2 r2 = r1 == r2 && p1 == p2
  StringType len1 == StringType len2 = len1 == len2
  NilType == NilType = True
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
instance (Shallow.Transformation t, Functor (Shallow.Domain t), Deep.Functor t (AST.Module l l),
          Shallow.Functor t (AST.Module l l (Shallow.Codomain t) (Shallow.Codomain t))) =>
         Deep.Functor t (Modules l) where
   t <$> ~(Modules ms) = Modules (mapModule <$> ms)
      where mapModule m = t Shallow.<$> ((t Deep.<$>) <$> m)

instance Rank2.Functor (Modules l f') where
   f <$> ~(Modules ms) = Modules (f <$> ms)

instance Rank2.Apply (Modules l f') where
   ~(Modules fs) <*> ~(Modules ms) = Modules (Map.intersectionWith Rank2.apply fs ms)

-- * Boring attribute types
type instance Atts (Inherited TypeCheck) (Modules l f' f) = InhTCRoot l
type instance Atts (Synthesized TypeCheck) (Modules l f' f) = SynTC l
type instance Atts (Inherited TypeCheck) (AST.Module l l f' f) = InhTC l
type instance Atts (Synthesized TypeCheck) (AST.Module l l f' f) = SynTCMod l
type instance Atts (Inherited TypeCheck) (AST.Declaration l l f' f) = (InhTC l, Map AST.Ident AST.Ident)
type instance Atts (Synthesized TypeCheck) (AST.Declaration l l f' f) = SynTCMod l
type instance Atts (Inherited TypeCheck) (AST.ProcedureHeading l l f' f) = (InhTC l, Map AST.Ident AST.Ident)
type instance Atts (Synthesized TypeCheck) (AST.ProcedureHeading l l f' f) = SynTCHead l
type instance Atts (Inherited TypeCheck) (AST.Block l l f' f) = InhTC l
type instance Atts (Synthesized TypeCheck) (AST.Block l l f' f) = SynTC l
type instance Atts (Inherited TypeCheck) (AST.FormalParameters l l f' f) = InhTC l
type instance Atts (Synthesized TypeCheck) (AST.FormalParameters l l f' f) = SynTCSig l
type instance Atts (Inherited TypeCheck) (AST.FPSection l l f' f) = InhTC l
type instance Atts (Synthesized TypeCheck) (AST.FPSection l l f' f) = SynTCSec l
type instance Atts (Inherited TypeCheck) (AST.Type l l f' f) = InhTC l
type instance Atts (Synthesized TypeCheck) (AST.Type l l f' f) = SynTCType l
type instance Atts (Inherited TypeCheck) (AST.FieldList l l f' f) = InhTC l
type instance Atts (Synthesized TypeCheck) (AST.FieldList l l f' f) = SynTCFields l
type instance Atts (Inherited TypeCheck) (AST.StatementSequence l l f' f) = InhTC l
type instance Atts (Synthesized TypeCheck) (AST.StatementSequence l l f' f) = SynTC l
type instance Atts (Inherited TypeCheck) (AST.Expression l l f' f) = InhTC l
type instance Atts (Synthesized TypeCheck) (AST.Expression l l f' f) = SynTCExp l
type instance Atts (Inherited TypeCheck) (AST.Element l l f' f) = InhTC l
type instance Atts (Synthesized TypeCheck) (AST.Element l l f' f) = SynTCExp l
type instance Atts (Inherited TypeCheck) (AST.Value l l f' f) = InhTC l
type instance Atts (Synthesized TypeCheck) (AST.Value l l f' f) = SynTCExp l
type instance Atts (Inherited TypeCheck) (AST.Designator l l f' f) = InhTC l
type instance Atts (Synthesized TypeCheck) (AST.Designator l l f' f) = SynTCDes l
type instance Atts (Inherited TypeCheck) (Deep.Product (AST.Expression l l) (AST.StatementSequence l l) f' f) = InhTC l
type instance Atts (Synthesized TypeCheck) (Deep.Product (AST.Expression l l) (AST.StatementSequence l l) f' f) = SynTC l
type instance Atts (Inherited TypeCheck) (AST.Statement l l f' f) = InhTC l
type instance Atts (Synthesized TypeCheck) (AST.Statement l l f' f) = SynTC l
type instance Atts (Inherited TypeCheck) (AST.Case l l f' f) = (InhTC l, Type l)
type instance Atts (Synthesized TypeCheck) (AST.Case l l f' f) = SynTC l
type instance Atts (Inherited TypeCheck) (AST.CaseLabels l l f' f) = (InhTC l, Type l)
type instance Atts (Synthesized TypeCheck) (AST.CaseLabels l l f' f) = SynTC l
type instance Atts (Inherited TypeCheck) (AST.WithAlternative l l f' f) = InhTC l
type instance Atts (Synthesized TypeCheck) (AST.WithAlternative l l f' f) = SynTC l

-- * Rules

instance Ord (Abstract.QualIdent l) =>
         Attribution TypeCheck (Modules l) ((,) Int) where
   attribution TypeCheck (_, Modules self) (Inherited inheritance, Modules ms) =
     (Synthesized SynTC{errors= foldMap (moduleErrors . syn) ms},
      Modules (Map.mapWithKey moduleInheritance self))
     where moduleInheritance name mod = Inherited InhTC{env= rootEnv inheritance <> foldMap (moduleEnv . syn) ms,
                                                        currentModule= name}

instance (Abstract.Oberon l, Abstract.Nameable l, Ord (Abstract.QualIdent l), Show (Abstract.QualIdent l),
          Atts (Synthesized TypeCheck) (Abstract.Declaration l l (Semantics TypeCheck) (Semantics TypeCheck))
          ~ SynTCMod l,
          Atts (Inherited TypeCheck) (Abstract.StatementSequence l l (Semantics TypeCheck) (Semantics TypeCheck)) ~ InhTC l,
          Atts (Inherited TypeCheck) (Abstract.Declaration l l (Semantics TypeCheck) (Semantics TypeCheck))
          ~ (InhTC l, Map AST.Ident AST.Ident),
          Atts (Synthesized TypeCheck) (Abstract.StatementSequence l l (Semantics TypeCheck) (Semantics TypeCheck))
          ~ SynTC l) =>
         Attribution TypeCheck (AST.Module l l) ((,) Int) where
   attribution TypeCheck (pos, AST.Module moduleName imports decls body) 
               (Inherited inheritance, AST.Module _ _ decls' body') =
      (Synthesized SynTCMod{moduleErrors= foldMap (moduleErrors . syn) decls' <> foldMap (errors . syn) body',
                            moduleEnv= exportedEnv,
                            pointerTargets= pointers},
       AST.Module moduleName imports [Inherited (localEnv, pointers)] (Inherited localEnv <$ body))
      where exportedEnv = exportNominal <$> Map.mapKeysMonotonic export newEnv
            newEnv = Map.unionsWith mergeTypeBoundProcedures (moduleEnv . syn <$> decls')
            localEnv = InhTC (newEnv `Map.union` env inheritance) (currentModule inheritance)
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
            pointers= foldMap (pointerTargets . syn) decls'
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

instance (Abstract.Nameable l, Ord (Abstract.QualIdent l),
          Atts (Inherited TypeCheck) (Abstract.Declaration l l (Semantics TypeCheck) (Semantics TypeCheck))
          ~ (InhTC l, Map AST.Ident AST.Ident),
          Atts (Inherited TypeCheck) (Abstract.Type l l (Semantics TypeCheck) (Semantics TypeCheck)) ~ InhTC l,
          Atts (Inherited TypeCheck) (Abstract.ProcedureHeading l l (Semantics TypeCheck) (Semantics TypeCheck))
          ~ (InhTC l, Map AST.Ident AST.Ident),
          Atts (Inherited TypeCheck) (Abstract.Block l l (Semantics TypeCheck) (Semantics TypeCheck)) ~ InhTC l,
          Atts (Inherited TypeCheck) (Abstract.FormalParameters l l (Semantics TypeCheck) (Semantics TypeCheck)) ~ InhTC l,
          Atts (Inherited TypeCheck) (Abstract.ConstExpression l l (Semantics TypeCheck) (Semantics TypeCheck)) ~ InhTC l,
          Atts (Synthesized TypeCheck) (Abstract.Declaration l l (Semantics TypeCheck) (Semantics TypeCheck))
          ~ SynTCMod l,
          Atts (Synthesized TypeCheck) (Abstract.Type l l (Semantics TypeCheck) (Semantics TypeCheck)) ~ SynTCType l,
          Atts (Synthesized TypeCheck) (Abstract.FormalParameters l l (Semantics TypeCheck) (Semantics TypeCheck))
          ~ SynTCSig l,
          Atts (Synthesized TypeCheck) (Abstract.ProcedureHeading l l (Semantics TypeCheck) (Semantics TypeCheck))
          ~ SynTCHead l,
          Atts (Synthesized TypeCheck) (Abstract.Block l l (Semantics TypeCheck) (Semantics TypeCheck)) ~ SynTC l,
          Atts (Synthesized TypeCheck) (Abstract.ConstExpression l l (Semantics TypeCheck) (Semantics TypeCheck))
          ~ SynTCExp l) =>
         Attribution TypeCheck (AST.Declaration l l) ((,) Int) where
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
      where nominal t@NominalType{} = t
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
      (Synthesized SynTCMod{moduleErrors= headingErrors (syn heading) <> errors (syn body),
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
          Atts (Inherited TypeCheck) (Abstract.FormalParameters l l (Semantics TypeCheck) (Semantics TypeCheck))
          ~ InhTC l,
          Atts (Synthesized TypeCheck) (Abstract.FormalParameters l l (Semantics TypeCheck) (Semantics TypeCheck))
          ~ SynTCSig l) =>
         Attribution TypeCheck (AST.ProcedureHeading l l) ((,) Int) where
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

instance (Ord (Abstract.QualIdent l),
          Atts (Inherited TypeCheck) (Abstract.Declaration l l (Semantics TypeCheck) (Semantics TypeCheck))
          ~ (InhTC l, Map AST.Ident AST.Ident),
          Atts (Inherited TypeCheck) (Abstract.StatementSequence l l (Semantics TypeCheck) (Semantics TypeCheck)) ~ InhTC l,
          Atts (Synthesized TypeCheck) (Abstract.Declaration l l (Semantics TypeCheck) (Semantics TypeCheck))
          ~ SynTCMod l,
          Atts (Synthesized TypeCheck) (Abstract.StatementSequence l l (Semantics TypeCheck) (Semantics TypeCheck))
          ~ SynTC l) =>
         Attribution TypeCheck (AST.Block l l) ((,) Int) where
   attribution TypeCheck (pos, AST.Block{}) (Inherited inheritance, AST.Block declarations statements) =
      (Synthesized SynTC{errors= foldMap (moduleErrors . syn) declarations <> foldMap (errors . syn) statements},
       AST.Block (pure $ Inherited (localInherited, mempty)) (pure $ Inherited localInherited))
      where localInherited = InhTC (foldMap (moduleEnv . syn) declarations <> env inheritance)
                                   (currentModule inheritance)
            
instance (Ord (Abstract.QualIdent l),
          Atts (Inherited TypeCheck) (Abstract.FPSection l l (Semantics TypeCheck) (Semantics TypeCheck)) ~ InhTC l,
          Atts (Synthesized TypeCheck) (Abstract.FPSection l l (Semantics TypeCheck) (Semantics TypeCheck)) ~ SynTCSec l) =>
         Attribution TypeCheck (AST.FormalParameters l l) ((,) Int) where
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
          Atts (Inherited TypeCheck) (Abstract.Type l l (Semantics TypeCheck) (Semantics TypeCheck)) ~ InhTC l,
          Atts (Synthesized TypeCheck) (Abstract.Type l l (Semantics TypeCheck) (Semantics TypeCheck)) ~ SynTCType l) =>
         Attribution TypeCheck (AST.FPSection l l) ((,) Int) where
   attribution TypeCheck (pos, AST.FPSection var names _typeDef) (Inherited inheritance, AST.FPSection _var _names typeDef) =
      (Synthesized SynTCSec{sectionErrors= typeErrors (syn typeDef),
                            sectionParameters= (var, definedType (syn typeDef)) <$ names,
                            sectionEnv= Map.fromList (flip (,) (definedType $ syn typeDef) . Abstract.nonQualIdent
                                                      <$> names)},
       AST.FPSection var names (Inherited inheritance))

instance (Abstract.Nameable l, Ord (Abstract.QualIdent l),
          Atts (Inherited TypeCheck) (Abstract.FormalParameters l l (Semantics TypeCheck) (Semantics TypeCheck)) ~ InhTC l,
          Atts (Inherited TypeCheck) (Abstract.FieldList l l (Semantics TypeCheck) (Semantics TypeCheck)) ~ InhTC l,
          Atts (Inherited TypeCheck) (Abstract.Type l l (Semantics TypeCheck) (Semantics TypeCheck)) ~ InhTC l,
          Atts (Inherited TypeCheck) (Abstract.ConstExpression l l (Semantics TypeCheck) (Semantics TypeCheck)) ~ InhTC l,
          Atts (Synthesized TypeCheck) (Abstract.FormalParameters l l (Semantics TypeCheck) (Semantics TypeCheck))
          ~ SynTCSig l,
          Atts (Synthesized TypeCheck) (Abstract.FieldList l l (Semantics TypeCheck) (Semantics TypeCheck)) ~ SynTCFields l,
          Atts (Synthesized TypeCheck) (Abstract.Type l l (Semantics TypeCheck) (Semantics TypeCheck)) ~ SynTCType l,
          Atts (Synthesized TypeCheck) (Abstract.ConstExpression l l (Semantics TypeCheck) (Semantics TypeCheck))
          ~ SynTCExp l) =>
         Attribution TypeCheck (AST.Type l l) ((,) Int) where
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
                             definedType= ArrayType (integerValue . syn <$> dimensions') (definedType $ syn itemType)},
       AST.ArrayType [Inherited inheritance] (Inherited inheritance))
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
          Atts (Inherited TypeCheck) (Abstract.Type l l (Semantics TypeCheck) (Semantics TypeCheck)) ~ InhTC l,
          Atts (Synthesized TypeCheck) (Abstract.Type l l (Semantics TypeCheck) (Semantics TypeCheck)) ~ SynTCType l) =>
         Attribution TypeCheck (AST.FieldList l l) ((,) Int) where
   attribution TypeCheck (pos, AST.FieldList names _declaredType) (Inherited inheritance, AST.FieldList _names declaredType) =
      (Synthesized SynTCFields{fieldErrors= typeErrors (syn declaredType),
                               fieldEnv= foldMap (\name-> Map.singleton (Abstract.getIdentDefName name)
                                                          (definedType $ syn declaredType)) 
                                         names},
       AST.FieldList names (Inherited inheritance))
   attribution TypeCheck self (Inherited inheritance, AST.EmptyFieldList) =
     (Synthesized SynTCFields{fieldErrors= [], fieldEnv= mempty},
      AST.EmptyFieldList)

instance Abstract.Nameable l =>
         Attribution TypeCheck (Deep.Product (AST.Expression l l) (AST.StatementSequence l l)) ((,) Int) where
   attribution TypeCheck (pos, _) (Inherited inheritance, Deep.Pair condition statements) =
      (Synthesized SynTC{errors= booleanExpressionErrors inheritance pos (syn condition) <> errors (syn statements)},
       Deep.Pair (Inherited inheritance) (Inherited inheritance))

instance (Atts (Inherited TypeCheck) (Abstract.Statement l l (Semantics TypeCheck) (Semantics TypeCheck)) ~ InhTC l,
          Atts (Synthesized TypeCheck) (Abstract.Statement l l (Semantics TypeCheck) (Semantics TypeCheck)) ~ SynTC l) =>
         Attribution TypeCheck (AST.StatementSequence l l) ((,) Int) where
   attribution TypeCheck (pos, AST.StatementSequence statements) (Inherited inheritance, AST.StatementSequence statements') =
      (Synthesized SynTC{errors= foldMap (errors . syn) statements'},
       AST.StatementSequence (pure $ Inherited inheritance))

instance (Abstract.Wirthy l, Abstract.Nameable l, Ord (Abstract.QualIdent l),
          Atts (Inherited TypeCheck) (Abstract.StatementSequence l l (Semantics TypeCheck) (Semantics TypeCheck)) ~ InhTC l,
          Atts (Inherited TypeCheck) (Deep.Product (Abstract.Expression l l) (Abstract.StatementSequence l l)
                                      (Semantics TypeCheck) (Semantics TypeCheck)) ~ InhTC l,
          Atts (Inherited TypeCheck) (Abstract.Case l l (Semantics TypeCheck) (Semantics TypeCheck)) ~ (InhTC l, Type l),
          Atts (Inherited TypeCheck) (Abstract.WithAlternative l l (Semantics TypeCheck) (Semantics TypeCheck)) ~ InhTC l,
          Atts (Inherited TypeCheck) (Abstract.Expression l l (Semantics TypeCheck) (Semantics TypeCheck)) ~ InhTC l,
          Atts (Inherited TypeCheck) (Abstract.Designator l l (Semantics TypeCheck) (Semantics TypeCheck)) ~ InhTC l,
          Atts (Synthesized TypeCheck) (Abstract.StatementSequence l l (Semantics TypeCheck) (Semantics TypeCheck))
          ~ SynTC l,
          Atts (Synthesized TypeCheck) (Deep.Product (Abstract.Expression l l) (Abstract.StatementSequence l l)
                                        (Semantics TypeCheck) (Semantics TypeCheck))
          ~ SynTC l,
          Atts (Synthesized TypeCheck) (Abstract.Case l l (Semantics TypeCheck) (Semantics TypeCheck)) ~ SynTC l,
          Atts (Synthesized TypeCheck) (Abstract.WithAlternative l l (Semantics TypeCheck) (Semantics TypeCheck)) ~ SynTC l,
          Atts (Synthesized TypeCheck) (Abstract.Expression l l (Semantics TypeCheck) (Semantics TypeCheck))
          ~ SynTCExp l,
          Atts (Synthesized TypeCheck) (Abstract.Designator l l (Semantics TypeCheck) (Semantics TypeCheck))
          ~ SynTCDes l) =>
         Attribution TypeCheck (AST.Statement l l) ((,) Int) where
   attribution TypeCheck _ (Inherited inheritance, AST.EmptyStatement) = (Synthesized SynTC{errors= []}, AST.EmptyStatement)
   attribution TypeCheck (pos, _) (Inherited inheritance, AST.Assignment var value) = {-# SCC "Assignment" #-}
      (Synthesized SynTC{errors= assignmentCompatible inheritance pos (designatorType $ syn var) (inferredType $ syn value)},
       AST.Assignment (Inherited inheritance) (Inherited inheritance))
   attribution TypeCheck 
      (pos, AST.ProcedureCall _proc parameters) 
      (Inherited inheritance, AST.ProcedureCall procedure' parameters') =
      (Synthesized SynTC{errors= (case syn procedure'
                                  of SynTCDes{designatorErrors= [],
                                              designatorType= t} -> procedureErrors t
                                     SynTCDes{designatorErrors= errs} -> errs)
                                 <> foldMap (foldMap (expressionErrors . syn)) parameters'},
       AST.ProcedureCall (Inherited inheritance) (Just [Inherited inheritance]))
     where procedureErrors (ProcedureType _ formalTypes Nothing)
             | length formalTypes /= maybe 0 length parameters,
               not (length formalTypes == 2 && (length <$> parameters) == Just 1
                    && designatorName (syn procedure') == Just (Nothing, "ASSERT")
                    || length formalTypes == 1 && (length <$> parameters) == Just 2
                    && designatorName (syn procedure') == Just (Nothing, "NEW")
                    && all (all (isIntegerType . inferredType . syn) . tail) parameters') =
                 [(currentModule inheritance, pos, ArgumentCountMismatch (length formalTypes) $ maybe 0 length parameters)]
             | otherwise = concat (zipWith (parameterCompatible inheritance pos) formalTypes
                                   $ maybe [] (inferredType . syn <$>) parameters')
           procedureErrors (NominalType _ (Just t)) = procedureErrors t
           procedureErrors t = [(currentModule inheritance, pos, NonProcedureType t)]
   attribution TypeCheck self (Inherited inheritance, AST.If branches fallback) =
      (Synthesized SynTC{errors= foldMap (errors . syn) branches <> foldMap (errors . syn) fallback},
       AST.If (pure $ Inherited inheritance) (Just $ Inherited inheritance))
   attribution TypeCheck self (Inherited inheritance, AST.CaseStatement value branches fallback) =
      (Synthesized SynTC{errors= expressionErrors (syn value) <> foldMap (errors . syn) branches
                                 <> foldMap (errors . syn) fallback},
       AST.CaseStatement (Inherited inheritance) (pure $ Inherited (inheritance, inferredType $ syn value))
                         (Just $ Inherited inheritance))
   attribution TypeCheck (pos, _) (Inherited inheritance, AST.While condition body) =
      (Synthesized SynTC{errors= booleanExpressionErrors inheritance pos (syn condition) <> errors (syn body)},
       AST.While (Inherited inheritance) (Inherited inheritance))
   attribution TypeCheck (pos, _) (Inherited inheritance, AST.Repeat body condition) =
      (Synthesized SynTC{errors= booleanExpressionErrors inheritance pos (syn condition) <> errors (syn body)},
       AST.Repeat (Inherited inheritance) (Inherited inheritance))
   attribution TypeCheck (pos, AST.For counter _start _end _step _body) 
                         (Inherited inheritance, AST.For _counter start end step body) =
      (Synthesized SynTC{errors= integerExpressionErrors inheritance pos (syn start) 
                                 <> integerExpressionErrors inheritance pos (syn end)
                                 <> foldMap (integerExpressionErrors inheritance pos . syn) step <> errors (syn body)},
       AST.For counter (Inherited inheritance) (Inherited inheritance) (Just $ Inherited inheritance)
                       (Inherited $ 
                        InhTC (Map.insert (Abstract.nonQualIdent counter)
                                          (NominalType (Abstract.nonQualIdent "INTEGER") Nothing)
                               $ env inheritance)
                              (currentModule inheritance)))
   attribution TypeCheck self (Inherited inheritance, AST.Loop body) = (Synthesized SynTC{errors= errors (syn body)},
                                                                        AST.Loop (Inherited inheritance))
   attribution TypeCheck self (Inherited inheritance, AST.With branches fallback) =
      (Synthesized SynTC{errors= foldMap (errors . syn) branches <> foldMap (errors . syn) fallback},
       AST.With (pure $ Inherited inheritance) (Just $ Inherited inheritance))
   attribution TypeCheck self (Inherited inheritance, AST.Exit) = (Synthesized SynTC{errors= []}, AST.Exit)
   attribution TypeCheck self (Inherited inheritance, AST.Return value) =
      (Synthesized SynTC{errors= foldMap (expressionErrors . syn) value}, 
       AST.Return (Just $ Inherited inheritance))

instance (Abstract.Nameable l, Ord (Abstract.QualIdent l),
          Atts (Inherited TypeCheck) (Abstract.StatementSequence l l (Semantics TypeCheck) (Semantics TypeCheck)) ~ InhTC l,
          Atts (Synthesized TypeCheck) (Abstract.StatementSequence l l (Semantics TypeCheck) (Semantics TypeCheck))
          ~ SynTC l) =>
         Attribution TypeCheck (AST.WithAlternative l l) ((,) Int) where
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

instance (Atts (Inherited TypeCheck) (Abstract.CaseLabels l l (Semantics TypeCheck) (Semantics TypeCheck))
          ~ (InhTC l, Type l),
          Atts (Inherited TypeCheck) (Abstract.StatementSequence l l (Semantics TypeCheck) (Semantics TypeCheck)) ~ InhTC l,
          Atts (Synthesized TypeCheck) (Abstract.CaseLabels l l (Semantics TypeCheck) (Semantics TypeCheck)) ~ SynTC l,
          Atts (Synthesized TypeCheck) (Abstract.StatementSequence l l (Semantics TypeCheck) (Semantics TypeCheck))
          ~ SynTC l) =>
         Attribution TypeCheck (AST.Case l l) ((,) Int) where
   attribution TypeCheck self (Inherited inheritance, AST.Case labels body) =
      (Synthesized SynTC{errors= foldMap (errors . syn) labels <> errors (syn body)},
       AST.Case (pure $ Inherited inheritance) (Inherited $ fst inheritance))
   attribution TypeCheck self (Inherited inheritance, AST.EmptyCase) = (Synthesized SynTC{errors= []}, AST.EmptyCase)

instance (Abstract.Nameable l, Eq (Abstract.QualIdent l),
          Atts (Inherited TypeCheck) (Abstract.ConstExpression l l (Semantics TypeCheck) (Semantics TypeCheck)) ~ InhTC l,
          Atts (Synthesized TypeCheck) (Abstract.ConstExpression l l (Semantics TypeCheck) (Semantics TypeCheck))
          ~ SynTCExp l) =>
         Attribution TypeCheck (AST.CaseLabels l l) ((,) Int) where
   attribution TypeCheck (pos, _) (Inherited inheritance, AST.SingleLabel value) =
      (Synthesized SynTC{errors= assignmentCompatible (fst inheritance) pos (snd inheritance) (inferredType $ syn value)},
       AST.SingleLabel (Inherited $ fst inheritance))
   attribution TypeCheck (pos, _) (Inherited (inheritance, caseType), AST.LabelRange start end) =
      (Synthesized SynTC{errors= assignmentCompatible inheritance pos caseType (inferredType $ syn start)
                                 <> assignmentCompatible inheritance pos caseType (inferredType $ syn end)},
       AST.LabelRange (Inherited inheritance) (Inherited inheritance))

instance (Abstract.Nameable l, Ord (Abstract.QualIdent l),
          Atts (Inherited TypeCheck) (Abstract.Expression l l (Semantics TypeCheck) (Semantics TypeCheck)) ~ InhTC l,
          Atts (Inherited TypeCheck) (Abstract.Element l l (Semantics TypeCheck) (Semantics TypeCheck)) ~ InhTC l,
          Atts (Inherited TypeCheck) (Abstract.Designator l l (Semantics TypeCheck) (Semantics TypeCheck)) ~ InhTC l,
          Atts (Inherited TypeCheck) (Abstract.Value l l (Semantics TypeCheck) (Semantics TypeCheck)) ~ InhTC l,
          Atts (Synthesized TypeCheck) (Abstract.Expression l l (Semantics TypeCheck) (Semantics TypeCheck))
          ~ SynTCExp l,
          Atts (Synthesized TypeCheck) (Abstract.Element l l (Semantics TypeCheck) (Semantics TypeCheck))
          ~ SynTCExp l,
          Atts (Synthesized TypeCheck) (Abstract.Value l l (Semantics TypeCheck) (Semantics TypeCheck)) ~ SynTCExp l,
          Atts (Synthesized TypeCheck) (Abstract.Designator l l (Semantics TypeCheck) (Semantics TypeCheck))
          ~ SynTCDes l) =>
         Attribution TypeCheck (AST.Expression l l) ((,) Int) where
   attribution TypeCheck (pos, AST.Relation op _ _) (Inherited inheritance, AST.Relation _op left right) =
      (Synthesized SynTCExp{expressionErrors= case expressionErrors (syn left) <> expressionErrors (syn right)
                                              of [] | t1 == t2 -> []
                                                    | AST.In <- op -> membershipCompatible (ultimate t1) (ultimate t2)
                                                    | equality op, [] <- assignmentCompatible inheritance pos t1 t2 -> []
                                                    | equality op, [] <- assignmentCompatible inheritance pos t2 t1 -> []
                                                    | otherwise -> comparable (ultimate t1) (ultimate t2)
                                                 errs -> errs,
                            inferredType= NominalType (Abstract.nonQualIdent "BOOLEAN") Nothing},
       AST.Relation op (Inherited inheritance) (Inherited inheritance))
      where t1 = inferredType (syn left)
            t2 = inferredType (syn right)
            equality AST.Equal = True
            equality AST.Unequal = True
            equality _ = False
            comparable (NominalType q1 Nothing) (NominalType q2 Nothing)
               | Abstract.getNonQualIdentName q1 == Just "BOOLEAN", Abstract.getNonQualIdentName q2 == Just "BOOLEAN" = []
               | Abstract.getNonQualIdentName q1 == Just "CHAR", Abstract.getNonQualIdentName q2 == Just "CHAR" = []
            comparable StringType{} StringType{} = []
            comparable (StringType 1) (NominalType q Nothing)
               | Abstract.getNonQualIdentName q == Just "CHAR" = []
            comparable (NominalType q Nothing) (StringType 1)
               | Abstract.getNonQualIdentName q == Just "CHAR" = []
            comparable StringType{} (ArrayType _ (NominalType q Nothing))
               | Abstract.getNonQualIdentName q == Just "CHAR" = []
            comparable (ArrayType _ (NominalType q Nothing)) StringType{}
               | Abstract.getNonQualIdentName q == Just "CHAR" = []
            comparable (ArrayType _ (NominalType q1 Nothing))
                       (ArrayType _ (NominalType q2 Nothing))
               | Abstract.getNonQualIdentName q1 == Just "CHAR", Abstract.getNonQualIdentName q2 == Just "CHAR" = []
            comparable (NominalType q1 Nothing) (NominalType q2 Nothing)
               | Just t1 <- Abstract.getNonQualIdentName q1,
                 Just t2 <- Abstract.getNonQualIdentName q2, isNumerical t1 && isNumerical t2 = []
            comparable (NominalType q1 Nothing) IntegerType{}
               | Just t1 <- Abstract.getNonQualIdentName q1, isNumerical t1 = []
            comparable IntegerType{} (NominalType q2 Nothing)
               | Just t2 <- Abstract.getNonQualIdentName q2, isNumerical t2 = []
            comparable t1 t2 = [(currentModule inheritance, pos, IncomparableTypes t1 t2)]
            membershipCompatible IntegerType{} (NominalType q Nothing)
               | Abstract.getNonQualIdentName q == Just "SET" = []
            membershipCompatible (NominalType q1 Nothing) (NominalType q2 Nothing)
               | Just t1 <- Abstract.getNonQualIdentName q1,
                 Abstract.getNonQualIdentName q2 == Just "SET", isNumerical t1 = []
   attribution TypeCheck (pos, AST.IsA _ q) (Inherited inheritance, AST.IsA left _) =
      (Synthesized SynTCExp{expressionErrors= case Map.lookup q (env inheritance)
                                              of Nothing -> [(currentModule inheritance, pos, UnknownName q)]
                                                 Just t -> assignmentCompatible inheritance pos (inferredType $ syn left) t,
                            inferredType= NominalType (Abstract.nonQualIdent "BOOLEAN") Nothing},
       AST.IsA (Inherited inheritance) q)
   attribution TypeCheck (pos, _) (Inherited inheritance, AST.Positive expr) =
      (Synthesized SynTCExp{expressionErrors= unaryNumericOperatorErrors inheritance pos (syn expr),
                            inferredType= inferredType (syn expr)},
       AST.Positive (Inherited inheritance))
   attribution TypeCheck (pos, _) (Inherited inheritance, AST.Negative expr) =
      (Synthesized SynTCExp{expressionErrors= unaryNumericOperatorErrors inheritance pos (syn expr),
                            inferredType= unaryNumericOperatorType negate (syn expr)},
       AST.Negative (Inherited inheritance))
   attribution TypeCheck (pos, _) (Inherited inheritance, AST.Add left right) =
      (Synthesized SynTCExp{expressionErrors= binarySetOrNumericOperatorErrors inheritance pos (syn left) (syn right),
                            inferredType= binaryNumericOperatorType div (syn left) (syn right)},
       AST.Add (Inherited inheritance) (Inherited inheritance))
   attribution TypeCheck (pos, _) (Inherited inheritance, AST.Subtract left right) =
      (Synthesized SynTCExp{expressionErrors= binarySetOrNumericOperatorErrors inheritance pos (syn left) (syn right),
                            inferredType= binaryNumericOperatorType div (syn left) (syn right)},
       AST.Subtract (Inherited inheritance) (Inherited inheritance))
   attribution TypeCheck (pos, _) (Inherited inheritance, AST.Or left right) =
      (Synthesized SynTCExp{expressionErrors= binaryBooleanOperatorErrors inheritance pos (syn left) (syn right),
                            inferredType= NominalType (Abstract.nonQualIdent "BOOLEAN") Nothing},
       AST.Or (Inherited inheritance) (Inherited inheritance))
   attribution TypeCheck (pos, _) (Inherited inheritance, AST.Multiply left right) =
      (Synthesized SynTCExp{expressionErrors= binarySetOrNumericOperatorErrors inheritance pos (syn left) (syn right),
                            inferredType= binaryNumericOperatorType div (syn left) (syn right)},
       AST.Multiply (Inherited inheritance) (Inherited inheritance))
   attribution TypeCheck (pos, _) (Inherited inheritance, AST.Divide left right) =
      (Synthesized SynTCExp{expressionErrors=
                               case (syn left, syn right)
                               of (SynTCExp{expressionErrors= [], inferredType= NominalType q1 Nothing},
                                   SynTCExp{expressionErrors= [], inferredType= NominalType q2 Nothing})
                                     | Abstract.getNonQualIdentName q1 == Just "REAL",
                                       Abstract.getNonQualIdentName q2 == Just "REAL" -> []
                                     | Abstract.getNonQualIdentName q1 == Just "SET",
                                       Abstract.getNonQualIdentName q2 == Just "SET" -> []
                                  (SynTCExp{expressionErrors= [], inferredType= t1},
                                   SynTCExp{expressionErrors= [], inferredType= t2})
                                    | t1 == t2 -> [(currentModule inheritance, pos, UnrealType t1)]
                                    | otherwise -> [(currentModule inheritance, pos, TypeMismatch t1 t2)],
                            inferredType= NominalType (Abstract.nonQualIdent "REAL") Nothing},
       AST.Divide (Inherited inheritance) (Inherited inheritance))
   attribution TypeCheck (pos, _) (Inherited inheritance, AST.IntegerDivide left right) =
      (Synthesized SynTCExp{expressionErrors= binaryIntegerOperatorErrors inheritance pos (syn left) (syn right),
                            inferredType= binaryNumericOperatorType div (syn left) (syn right)},
       AST.IntegerDivide (Inherited inheritance) (Inherited inheritance))
   attribution TypeCheck (pos, _) (Inherited inheritance, AST.Modulo left right) =
      (Synthesized SynTCExp{expressionErrors= binaryIntegerOperatorErrors inheritance pos (syn left) (syn right),
                            inferredType= binaryNumericOperatorType mod (syn left) (syn right)},
        AST.Modulo (Inherited inheritance) (Inherited inheritance))
   attribution TypeCheck (pos, _) (Inherited inheritance, AST.And left right) =
      (Synthesized SynTCExp{expressionErrors= binaryBooleanOperatorErrors inheritance pos (syn left) (syn right),
                            inferredType= NominalType (Abstract.nonQualIdent "BOOLEAN") Nothing},
       AST.And (Inherited inheritance) (Inherited inheritance))
   attribution TypeCheck self (Inherited inheritance, AST.Set elements) =
      (Synthesized SynTCExp{expressionErrors= mempty,
                            inferredType= NominalType (Abstract.nonQualIdent "SET") Nothing},
       AST.Set [Inherited inheritance])
   attribution TypeCheck self (Inherited inheritance, AST.Read designator) =
      (Synthesized SynTCExp{expressionErrors= designatorErrors (syn designator),
                            inferredType= designatorType (syn designator)},
       AST.Read (Inherited inheritance))
   attribution TypeCheck self (Inherited inheritance, AST.Literal value) =
      (Synthesized SynTCExp{expressionErrors= expressionErrors (syn value),
                            inferredType= inferredType (syn value)},
       AST.Literal (Inherited inheritance))
   attribution TypeCheck (pos, AST.FunctionCall _designator parameters)
               (Inherited inheritance, AST.FunctionCall designator parameters') =
      (Synthesized SynTCExp{expressionErrors=
                                case {-# SCC "FunctionCall" #-} syn designator
                                of SynTCDes{designatorErrors= [],
                                            designatorType= ProcedureType _ formalTypes Just{}}
                                     | length formalTypes /= length parameters ->
                                         [(currentModule inheritance, pos,
                                           ArgumentCountMismatch (length formalTypes)
                                                                 (length parameters))]
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
                                     | ProcedureType _ _ (Just returnType) <- ultimate t ->
                                         case returnType
                                         of UnknownType | Just (Nothing, name) <- d
                                                          -> builtinType name (inferredType . syn <$> parameters')
                                            _ -> returnType
                                   _ -> UnknownType},
       AST.FunctionCall (Inherited inheritance) [Inherited inheritance])
     where builtinType :: Abstract.Nameable l => Abstract.Ident -> [Type l] -> Type l
           builtinType "MAX" [t@(NominalType q Nothing)] =
                case Abstract.getNonQualIdentName q
                of Just "SET" -> IntegerType 63
                   Just "SHORTINT" -> IntegerType (2^15-1)
                   Just "INTEGER" -> IntegerType (2^31-1)
                   Just "LONGINT" -> IntegerType (2^63-1)
                   _ -> t
           builtinType "MIN" [t@(NominalType q Nothing)] =
                case Abstract.getNonQualIdentName q
                of Just "SET" -> IntegerType 0
                   Just "SHORTINT" -> IntegerType (-2^15)
                   Just "INTEGER" -> IntegerType (-2^31)
                   Just "LONGINT" -> IntegerType (-2^63)
                   _ -> t
           systemCallType "VAL" [t1, t2] = Just t1
           systemCallType _ _ = Nothing
   attribution TypeCheck (pos, _) (Inherited inheritance, AST.Not expr) =
      (Synthesized SynTCExp{expressionErrors= booleanExpressionErrors inheritance pos (syn expr),
                            inferredType= NominalType (Abstract.nonQualIdent "BOOLEAN") Nothing},
       AST.Not (Inherited inheritance))

instance (Abstract.Wirthy l,
          Atts (Inherited TypeCheck) (Abstract.Expression l l (Semantics TypeCheck) (Semantics TypeCheck)) ~ InhTC l,
          Atts (Synthesized TypeCheck) (Abstract.Expression l l (Semantics TypeCheck) (Semantics TypeCheck))
          ~ SynTCExp l) =>
         Attribution TypeCheck (AST.Value l l) ((,) Int) where
   attribution TypeCheck (pos, AST.Integer x) (Inherited inheritance, _) =
      (Synthesized SynTCExp{expressionErrors= mempty,
                            inferredType= IntegerType $ fromIntegral x},
       AST.Integer x)
   attribution TypeCheck self (Inherited inheritance, AST.Real x) =
      (Synthesized SynTCExp{expressionErrors= mempty,
                            inferredType= NominalType (Abstract.nonQualIdent "REAL") Nothing},
       AST.Real x)
   attribution TypeCheck self (Inherited inheritance, AST.Boolean x) =
      (Synthesized SynTCExp{expressionErrors= mempty,
                            inferredType= NominalType (Abstract.nonQualIdent "BOOLEAN") Nothing},
       AST.Boolean x)
   attribution TypeCheck self (Inherited inheritance, AST.CharCode x) =
      (Synthesized SynTCExp{expressionErrors= mempty,
                            inferredType= NominalType (Abstract.nonQualIdent "CHAR") Nothing},
       AST.CharCode x)
   attribution TypeCheck (pos, AST.String x) (Inherited inheritance, _) =
      (Synthesized SynTCExp{expressionErrors= mempty,
                            inferredType= StringType (Text.length x)},
       AST.String x)
   attribution TypeCheck self (Inherited inheritance, AST.Nil) =
      (Synthesized SynTCExp{expressionErrors= mempty,
                            inferredType= NilType},
       AST.Nil)
   attribution TypeCheck (pos, AST.Builtin x) (Inherited inheritance, _) =
      (Synthesized SynTCExp{expressionErrors= mempty,
                            inferredType= NominalType (Abstract.nonQualIdent x) Nothing},
       AST.Builtin x)

instance (Abstract.Wirthy l, Abstract.Nameable l,
          Atts (Inherited TypeCheck) (Abstract.Expression l l (Semantics TypeCheck) (Semantics TypeCheck)) ~ InhTC l,
          Atts (Synthesized TypeCheck) (Abstract.Expression l l (Semantics TypeCheck) (Semantics TypeCheck))
          ~ SynTCExp l) =>
         Attribution TypeCheck (AST.Element l l) ((,) Int) where
   attribution TypeCheck (pos, _) (Inherited inheritance, AST.Element expr) =
      (Synthesized SynTCExp{expressionErrors= integerExpressionErrors inheritance pos (syn expr),
                            inferredType= NominalType (Abstract.nonQualIdent "SET") Nothing},
       AST.Element (Inherited inheritance))
   attribution TypeCheck (pos, _) (Inherited inheritance, AST.Range low high) =
      (Synthesized SynTCExp{expressionErrors= integerExpressionErrors inheritance pos (syn low)
                                              <> integerExpressionErrors inheritance pos (syn high),
                            inferredType= NominalType (Abstract.nonQualIdent "SET") Nothing},
       AST.Range (Inherited inheritance) (Inherited inheritance))

instance (Abstract.Nameable l, Abstract.Oberon l, Ord (Abstract.QualIdent l),
          Atts (Inherited TypeCheck) (Abstract.Expression l l (Semantics TypeCheck) (Semantics TypeCheck)) ~ InhTC l,
          Atts (Inherited TypeCheck) (Abstract.Designator l l (Semantics TypeCheck) (Semantics TypeCheck)) ~ InhTC l,
          Atts (Synthesized TypeCheck) (Abstract.Expression l l (Semantics TypeCheck) (Semantics TypeCheck))
          ~ SynTCExp l,
          Atts (Synthesized TypeCheck) (Abstract.Designator l l (Semantics TypeCheck) (Semantics TypeCheck))
          ~ SynTCDes l) =>
         Attribution TypeCheck (AST.Designator l l) ((,) Int) where
   attribution TypeCheck (pos, AST.Variable q) (Inherited inheritance, _) =
      (Synthesized SynTCDes{designatorErrors= case designatorType
                                              of Nothing -> [(currentModule inheritance, pos, UnknownName q)]
                                                 Just{} -> [],
                            designatorName= (,) Nothing <$> Abstract.getNonQualIdentName q
                                            <|> first Just <$> Abstract.getQualIdentNames q,
                            designatorType= fromMaybe UnknownType designatorType},
       AST.Variable q)
      where designatorType = Map.lookup q (env inheritance)
   attribution TypeCheck (pos, AST.Field _record fieldName) (Inherited inheritance, AST.Field record _fieldName) =
      (Synthesized SynTCDes{designatorErrors= case syn record
                                              of SynTCDes{designatorErrors= [],
                                                          designatorType= t} ->
                                                   maybe [(currentModule inheritance, pos, NonRecordType t)]
                                                         (maybe [(currentModule inheritance, pos, UnknownField fieldName t)] $ const [])
                                                         (access True t)
                                                 SynTCDes{designatorErrors= errors} -> errors,
                            designatorName= Nothing,
                            designatorType= fromMaybe UnknownType (fromMaybe Nothing $ access True
                                                                   $ designatorType $ syn record)},
       AST.Field (Inherited inheritance) fieldName)
     where access _ (RecordType _ fields) = Just (Map.lookup fieldName fields)
           access True (PointerType t) = access False t
           access allowPtr (NominalType _ (Just t)) = access allowPtr t
           access allowPtr (ReceiverType t) = (receive <$>) <$> access allowPtr t
           access _ _ = Nothing
           receive (ProcedureType _ params result) = ProcedureType True params result
           receive t = t
   attribution TypeCheck (pos, AST.Index _array indexes) (Inherited inheritance, AST.Index array _indexes) =
      (Synthesized SynTCDes{designatorErrors= case syn array
                                              of SynTCDes{designatorErrors= [],
                                                          designatorType= t} ->
                                                   either id (const []) (access True t)
                                                 SynTCDes{designatorErrors= errors} -> errors,
                            designatorType= either (const UnknownType) id (access True $ designatorType $ syn array)},
       AST.Index (Inherited inheritance) (pure $ Inherited inheritance))
      where access _ (ArrayType dimensions t)
              | length dimensions == length indexes = Right t
              | length dimensions == 0 && length indexes == 1 = Right t
              | otherwise = Left [(currentModule inheritance, pos, ExtraDimensionalIndex (length dimensions) (length indexes))]
            access allowPtr (NominalType _ (Just t)) = access allowPtr t
            access allowPtr (ReceiverType t) = access allowPtr t
            access True (PointerType t) = access False t
            access _ t = Left [(currentModule inheritance, pos, NonArrayType t)]
   attribution TypeCheck (pos, AST.TypeGuard _designator q) (Inherited inheritance, AST.TypeGuard designator _q) =
      (Synthesized SynTCDes{designatorErrors= case (syn designator, targetType)
                                              of (SynTCDes{designatorErrors= [],
                                                           designatorType= t}, 
                                                  Just t') -> assignmentCompatible inheritance pos t t'
                                                 (SynTCDes{designatorErrors= errors}, 
                                                  Nothing) -> (currentModule inheritance, pos, UnknownName q) : errors
                                                 (SynTCDes{designatorErrors= errors}, _) -> errors,
                            designatorType= fromMaybe UnknownType targetType},
       AST.TypeGuard (Inherited inheritance) q)
      where targetType = Map.lookup q (env inheritance)
   attribution TypeCheck (pos, _) (Inherited inheritance, AST.Dereference pointer) =
      (Synthesized SynTCDes{designatorErrors= case syn pointer
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
                                               _ -> UnknownType},
       AST.Dereference (Inherited inheritance))

unaryNumericOperatorErrors :: Abstract.Nameable l => InhTC l -> Int -> SynTCExp l -> [Error l]
unaryNumericOperatorErrors _ _ SynTCExp{expressionErrors= [], inferredType= IntegerType{}} = []
unaryNumericOperatorErrors _ _ SynTCExp{expressionErrors= [],
                                        inferredType= NominalType q Nothing}
  | Just name <- Abstract.getNonQualIdentName q, isNumerical name = []
unaryNumericOperatorErrors inheritance pos SynTCExp{expressionErrors= [], inferredType= t} = 
   [(currentModule inheritance, pos, NonNumericType t)]
unaryNumericOperatorErrors _ _ SynTCExp{expressionErrors= errs} = errs

unaryNumericOperatorType :: (Int -> Int) -> SynTCExp l -> Type l
unaryNumericOperatorType f SynTCExp{inferredType= IntegerType x} = IntegerType (f x)
unaryNumericOperatorType _ SynTCExp{inferredType= t} = t

binarySetOrNumericOperatorErrors :: (Abstract.Nameable l, Eq (Abstract.QualIdent l))
                                 => InhTC l -> Int -> SynTCExp l -> SynTCExp l -> [Error l]
binarySetOrNumericOperatorErrors _ _
  SynTCExp{expressionErrors= [], inferredType= NominalType q1 Nothing}
  SynTCExp{expressionErrors= [], inferredType= NominalType q2 Nothing}
  | Just name1 <- Abstract.getNonQualIdentName q1, Just name2 <- Abstract.getNonQualIdentName q2,
    isNumerical name1 && isNumerical name2 || name1 == "SET" && name2 == "SET" = []
binarySetOrNumericOperatorErrors _ _
  SynTCExp{expressionErrors= [], inferredType= IntegerType{}}
  SynTCExp{expressionErrors= [], inferredType= NominalType q Nothing}
  | Just name <- Abstract.getNonQualIdentName q, isNumerical name = []
binarySetOrNumericOperatorErrors _ _
  SynTCExp{expressionErrors= [], inferredType= NominalType q Nothing}
  SynTCExp{expressionErrors= [], inferredType= IntegerType{}}
  | Just name <- Abstract.getNonQualIdentName q, isNumerical name = []
binarySetOrNumericOperatorErrors _ _
  SynTCExp{expressionErrors= [], inferredType= IntegerType{}}
  SynTCExp{expressionErrors= [], inferredType= IntegerType{}} = []
binarySetOrNumericOperatorErrors inheritance pos SynTCExp{expressionErrors= [], inferredType= t1}
                                 SynTCExp{expressionErrors= [], inferredType= t2}
  | t1 == t2 = [(currentModule inheritance, pos, NonNumericType t1)]
  | otherwise = [(currentModule inheritance, pos, TypeMismatch t1 t2)]
binarySetOrNumericOperatorErrors _ _ SynTCExp{expressionErrors= errs1} SynTCExp{expressionErrors= errs2} = errs1 <> errs2

binaryNumericOperatorType :: (Abstract.Nameable l, Eq (Abstract.QualIdent l))
                          => (Int -> Int -> Int) -> SynTCExp l -> SynTCExp l -> Type l
binaryNumericOperatorType f SynTCExp{inferredType= IntegerType x} SynTCExp{inferredType= IntegerType y} =
  IntegerType (f x y)
binaryNumericOperatorType _ SynTCExp{inferredType= t1} SynTCExp{inferredType= t2}
  | t1 == t2 = t1
  | IntegerType{} <- t1 = t2
  | IntegerType{} <- t2 = t1
  | NominalType q1 Nothing <- t1, Just name1 <- Abstract.getNonQualIdentName q1,
    NominalType q2 Nothing <- t2, Just name2 <- Abstract.getNonQualIdentName q2,
    Just index1 <- List.elemIndex name1 numericTypeNames,
    Just index2 <- List.elemIndex name2 numericTypeNames =
      NominalType (Abstract.nonQualIdent $ numericTypeNames !! max index1 index2) Nothing
  | otherwise = t1

binaryIntegerOperatorErrors :: Abstract.Nameable l => InhTC l -> Int ->  SynTCExp l -> SynTCExp l -> [Error l]
binaryIntegerOperatorErrors inheritance pos syn1 syn2 = integerExpressionErrors inheritance pos syn1 
                                                      <> integerExpressionErrors inheritance pos syn2

integerExpressionErrors inheritance pos SynTCExp{expressionErrors= [], inferredType= t}
  | isIntegerType t = []
  | otherwise = [(currentModule inheritance, pos, NonIntegerType t)]
integerExpressionErrors _ _ SynTCExp{expressionErrors= errs} = errs

isIntegerType IntegerType{} = True
isIntegerType (NominalType q Nothing) | Abstract.getNonQualIdentName q == Just "SHORTINT" = True
isIntegerType (NominalType q Nothing) | Abstract.getNonQualIdentName q == Just "INTEGER" = True
isIntegerType (NominalType q Nothing) | Abstract.getNonQualIdentName q == Just "LONGINT" = True
isIntegerType t = False

booleanExpressionErrors _ _ SynTCExp{expressionErrors= [],
                                     inferredType= NominalType q Nothing}
  | Abstract.getNonQualIdentName q == Just "BOOLEAN" = []
booleanExpressionErrors inheritance pos SynTCExp{expressionErrors= [], inferredType= t} = 
   [(currentModule inheritance, pos, NonBooleanType t)]
booleanExpressionErrors _ _ SynTCExp{expressionErrors= errs} = errs

binaryBooleanOperatorErrors :: (Abstract.Nameable l, Eq (Abstract.QualIdent l))
                            => InhTC l -> Int -> SynTCExp l -> SynTCExp l -> [Error l]
binaryBooleanOperatorErrors _inh _pos
  SynTCExp{expressionErrors= [], inferredType= NominalType q1 Nothing}
  SynTCExp{expressionErrors= [], inferredType= NominalType q2 Nothing}
  | Abstract.getNonQualIdentName q1 == Just "BOOLEAN", Abstract.getNonQualIdentName q2 == Just "BOOLEAN" = []
binaryBooleanOperatorErrors inheritance pos
  SynTCExp{expressionErrors= [], inferredType= t1}
  SynTCExp{expressionErrors= [], inferredType= t2}
  | t1 == t2 = [(currentModule inheritance, pos, NonBooleanType t1)]
  | otherwise = [(currentModule inheritance, pos, TypeMismatch t1 t2)]
binaryBooleanOperatorErrors _ _ SynTCExp{expressionErrors= errs1} SynTCExp{expressionErrors= errs2} = errs1 <> errs2

parameterCompatible :: (Abstract.Nameable l, Eq (Abstract.QualIdent l))
                    => InhTC l -> Int -> (Bool, Type l) -> Type l -> [Error l]
parameterCompatible _ _ (_, expected@(ArrayType [] _)) actual
  | arrayCompatible expected actual = []
parameterCompatible inheritance pos (True, expected) actual
  | expected == actual = []
  | otherwise = [(currentModule inheritance, pos, UnequalTypes expected actual)]
parameterCompatible inheritance pos (False, expected) actual
  | NominalType q Nothing <- expected, Abstract.getNonQualIdentName q == Just "ARRAY", ArrayType{} <- actual = []
  | otherwise = assignmentCompatible inheritance pos expected actual

assignmentCompatible :: (Abstract.Nameable l, Eq (Abstract.QualIdent l))
                     => InhTC l -> Int -> Type l -> Type l -> [Error l]
assignmentCompatible inheritance pos expected actual
   | expected == actual = []
   | NominalType q1 Nothing <- expected, Just name1 <- Abstract.getNonQualIdentName q1,
     NominalType q2 Nothing <- actual, Just name2 <- Abstract.getNonQualIdentName q2,
     Just index1 <- List.elemIndex name1 numericTypeNames,
     Just index2 <- List.elemIndex name2 numericTypeNames, 
     index1 >= index2 = []
   | NominalType q Nothing <- expected, Just name <- Abstract.getNonQualIdentName q,
     IntegerType{} <- actual, isNumerical name = []
   | NominalType q Nothing <- expected, Abstract.getNonQualIdentName q == Just "BASIC TYPE",
     NominalType q Nothing <- actual, Just name <- Abstract.getNonQualIdentName q,
     name `elem` ["BOOLEAN", "CHAR", "SHORTINT", "INTEGER", "LONGINT", "REAL", "LONGREAL", "SET"] = []
   | NominalType q Nothing <- expected, Abstract.getNonQualIdentName q == Just "POINTER", PointerType{} <- actual = []
   | NominalType q Nothing <- expected, Abstract.getNonQualIdentName q == Just "POINTER",
     NominalType _ (Just t) <- actual =
       assignmentCompatible inheritance pos expected t
   | NominalType q Nothing <- expected, Abstract.getNonQualIdentName q == Just "CHAR", actual == StringType 1 = []
   | ReceiverType t <- actual = assignmentCompatible inheritance pos expected t
   | ReceiverType t <- expected = assignmentCompatible inheritance pos t actual
   | NilType <- actual, PointerType{} <- expected = []
   | NilType <- actual, ProcedureType{} <- expected = []
   | NilType <- actual, NominalType _ (Just t) <- expected = assignmentCompatible inheritance pos t actual
--   | ArrayType [] (NominalType (Abstract.nonQualIdent "CHAR") Nothing) <- expected, StringType{} <- actual = []
   | ArrayType [m] (NominalType q Nothing) <- expected, Abstract.getNonQualIdentName q == Just "CHAR",
     StringType n <- actual =
      if m < n then [(currentModule inheritance, pos, TooSmallArrayType m n)] else []
   | targetExtends actual expected = []
   | NominalType _ (Just t) <- expected, ProcedureType{} <- actual = assignmentCompatible inheritance pos t actual
   | otherwise = [(currentModule inheritance, pos, IncompatibleTypes expected actual)]

arrayCompatible (ArrayType [] t1) (ArrayType _ t2) = t1 == t2 || arrayCompatible t1 t2
arrayCompatible (ArrayType [] (NominalType q Nothing)) StringType{}
   | Abstract.getNonQualIdentName q == Just "CHAR" = True
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

instance Shallow.Transformation TypeCheck where
   type Domain TypeCheck = Placed
   type Codomain TypeCheck = Semantics TypeCheck

-- * More boring Shallow.Functor instances, TH candidates
instance Ord (Abstract.QualIdent l) =>
         Shallow.Functor TypeCheck (Modules l (Semantics TypeCheck) (Semantics TypeCheck)) where
   (<$>) = AG.mapDefault snd
instance Abstract.Nameable l =>
         Shallow.Functor TypeCheck (Deep.Product (AST.Expression l l) (AST.StatementSequence l l)
                                       (Semantics TypeCheck) (Semantics TypeCheck)) where
   (<$>) = AG.mapDefault snd

-- * Unsafe Rank2 AST instances

instance Rank2.Apply (AST.Module l l f') where
   AST.Module name1 imports1 decls1 body1 <*> ~(AST.Module name2 imports2 decls2 body2) =
      AST.Module name1 imports1 (liftA2 Rank2.apply decls1 decls2) (liftA2 Rank2.apply body1 body2)

type Placed = ((,) Int)

checkModules :: (Abstract.Oberon l, Abstract.Nameable l,
                 Ord (Abstract.QualIdent l), Show (Abstract.QualIdent l),
                 Atts (Inherited TypeCheck) (Abstract.Declaration l l (Semantics TypeCheck) (Semantics TypeCheck))
                 ~ (InhTC l, Map AST.Ident AST.Ident),
                 Atts (Inherited TypeCheck) (Abstract.StatementSequence l l (Semantics TypeCheck) (Semantics TypeCheck))
                 ~ InhTC l,
                 Atts (Synthesized TypeCheck) (Abstract.Declaration l l (Semantics TypeCheck) (Semantics TypeCheck))
                 ~ SynTCMod l,
                 Atts (Synthesized TypeCheck) (Abstract.StatementSequence l l (Semantics TypeCheck) (Semantics TypeCheck))
                 ~ SynTC l,
                 Full.Functor TypeCheck (Abstract.Declaration l l),
                 Full.Functor TypeCheck (Abstract.StatementSequence l l))
             => Environment l -> Map AST.Ident (AST.Module l l Placed Placed) -> [Error l]
checkModules predef modules =
   errors (syn (TypeCheck Shallow.<$> (0, TypeCheck Deep.<$> Modules modules')
                `Rank2.apply`
                Inherited (InhTCRoot predef)))
   where modules' = ((,) 0) <$> modules

predefined, predefined2 :: (Abstract.Wirthy l, Ord (Abstract.QualIdent l)) => Environment l
-- | The set of 'Predefined' types and procedures defined in the Oberon Language Report.
predefined = Map.fromList $ map (first Abstract.nonQualIdent) $
   [("BOOLEAN", NominalType (Abstract.nonQualIdent "BOOLEAN") Nothing),
    ("CHAR", NominalType (Abstract.nonQualIdent "CHAR") Nothing),
    ("SHORTINT", NominalType (Abstract.nonQualIdent "SHORTINT") Nothing),
    ("INTEGER", NominalType (Abstract.nonQualIdent "INTEGER") Nothing),
    ("LONGINT", NominalType (Abstract.nonQualIdent "LONGINT") Nothing),
    ("REAL", NominalType (Abstract.nonQualIdent "REAL") Nothing),
    ("LONGREAL", NominalType (Abstract.nonQualIdent "LONGREAL") Nothing),
    ("SET", NominalType (Abstract.nonQualIdent "SET") Nothing),
    ("TRUE", NominalType (Abstract.nonQualIdent "BOOLEAN") Nothing),
    ("FALSE", NominalType (Abstract.nonQualIdent "BOOLEAN") Nothing),
    ("ABS", ProcedureType False [(False, NominalType (Abstract.nonQualIdent "INTEGER") Nothing)] $
            Just $ NominalType (Abstract.nonQualIdent "INTEGER") Nothing),
    ("ASH", ProcedureType False [(False, NominalType (Abstract.nonQualIdent "INTEGER") Nothing)] $
            Just $ NominalType (Abstract.nonQualIdent "INTEGER") Nothing),
    ("CAP", ProcedureType False [(False, NominalType (Abstract.nonQualIdent "CHAR") Nothing)] $
            Just $ NominalType (Abstract.nonQualIdent "CHAR") Nothing),
    ("LEN", ProcedureType False [(False, NominalType (Abstract.nonQualIdent "ARRAY") Nothing)] $
            Just $ NominalType (Abstract.nonQualIdent "LONGINT") Nothing),
    ("MAX", ProcedureType False [(False, NominalType (Abstract.nonQualIdent "BASIC TYPE") Nothing)] $ Just UnknownType),
    ("MIN", ProcedureType False [(False, NominalType (Abstract.nonQualIdent "BASIC TYPE") Nothing)] $ Just UnknownType),
    ("ODD", ProcedureType False [(False, NominalType (Abstract.nonQualIdent "CHAR") Nothing)] $
            Just $ NominalType (Abstract.nonQualIdent "BOOLEAN") Nothing),
    ("SIZE", ProcedureType False [(False, NominalType (Abstract.nonQualIdent "CHAR") Nothing)] $
             Just $ NominalType (Abstract.nonQualIdent "INTEGER") Nothing),
    ("ORD", ProcedureType False [(False, NominalType (Abstract.nonQualIdent "CHAR") Nothing)] $
            Just $ NominalType (Abstract.nonQualIdent "INTEGER") Nothing),
    ("CHR", ProcedureType False [(False, NominalType (Abstract.nonQualIdent "INTEGER") Nothing)] $
            Just $ NominalType (Abstract.nonQualIdent "CHAR") Nothing),
    ("SHORT", ProcedureType False [(False, NominalType (Abstract.nonQualIdent "INTEGER") Nothing)]
              $ Just $ NominalType (Abstract.nonQualIdent "INTEGER") Nothing),
    ("LONG", ProcedureType False [(False, NominalType (Abstract.nonQualIdent "INTEGER") Nothing)] $
             Just $ NominalType (Abstract.nonQualIdent "INTEGER") Nothing),
    ("ENTIER", ProcedureType False [(False, NominalType (Abstract.nonQualIdent "REAL") Nothing)] $
               Just $ NominalType (Abstract.nonQualIdent "INTEGER") Nothing),
    ("INC", ProcedureType False [(False, NominalType (Abstract.nonQualIdent "LONGINT") Nothing)] Nothing),
    ("DEC", ProcedureType False [(False, NominalType (Abstract.nonQualIdent "LONGINT") Nothing)] Nothing),
    ("INCL", ProcedureType False [(False, NominalType (Abstract.nonQualIdent "SET") Nothing),
                                  (False, NominalType (Abstract.nonQualIdent "INTEGER") Nothing)] Nothing),
    ("EXCL", ProcedureType False [(False, NominalType (Abstract.nonQualIdent "SET") Nothing),
                                  (False, NominalType (Abstract.nonQualIdent "INTEGER") Nothing)] Nothing),
    ("COPY", ProcedureType False [(False, NominalType (Abstract.nonQualIdent "ARRAY") Nothing),
                                  (False, NominalType (Abstract.nonQualIdent "ARRAY") Nothing)] Nothing),
    ("NEW", ProcedureType False [(False, NominalType (Abstract.nonQualIdent "POINTER") Nothing)] Nothing),
    ("HALT", ProcedureType False [(False, NominalType (Abstract.nonQualIdent "INTEGER") Nothing)] Nothing)]

-- | The set of 'Predefined' types and procedures defined in the Oberon-2 Language Report.
predefined2 = predefined <>
   Map.fromList (first Abstract.nonQualIdent <$>
                 [("ASSERT", ProcedureType False [(False, NominalType (Abstract.nonQualIdent "BOOLEAN") Nothing),
                                                  (False, NominalType (Abstract.nonQualIdent "INTEGER") Nothing)] Nothing)])

instance (Deep.Functor TypeCheck (Deep.Product (AST.Expression l l) (AST.StatementSequence l l)),
          Shallow.Functor TypeCheck (Deep.Product (AST.Expression l l) (AST.StatementSequence l l) (Semantics TypeCheck) (Semantics TypeCheck))) =>
         Full.Functor TypeCheck (Deep.Product (AST.Expression l l) (AST.StatementSequence l l)) where
  (<$>) = Full.mapUpDefault

$(do l <- varT <$> newName "l"
     mconcat <$> mapM (\t-> Transformation.Full.TH.deriveUpFunctor (conT ''TypeCheck) $ conT t `appT` l `appT` l)
        [''AST.Declaration, ''AST.Type, ''AST.FieldList,
         ''AST.ProcedureHeading, ''AST.FormalParameters, ''AST.FPSection,
         ''AST.Expression, ''AST.Element, ''AST.Designator,
         ''AST.Block, ''AST.StatementSequence, ''AST.Statement,
         ''AST.Case, ''AST.CaseLabels, ''AST.Value, ''AST.WithAlternative])

$(do let sem = [t|Semantics TypeCheck|]
     let inst g = [d| instance Attribution TypeCheck ($g l l) ((,) Int) =>
                               Shallow.Functor TypeCheck ($g l l $sem $sem)
                         where (<$>) = AG.mapDefault snd |]
     mconcat <$> mapM (inst . conT)
        [''AST.Module, ''AST.Declaration, ''AST.Type, ''AST.FieldList,
         ''AST.ProcedureHeading, ''AST.FormalParameters, ''AST.FPSection,
         ''AST.Block, ''AST.StatementSequence, ''AST.Statement,
         ''AST.Case, ''AST.CaseLabels, ''AST.WithAlternative,
         ''AST.Expression, ''AST.Element, ''AST.Designator, ''AST.Value])
