{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, OverloadedStrings,
             TemplateHaskell, TypeFamilies, UndecidableInstances #-}

module Language.Oberon.TypeChecker (Error(..), errorMessage, checkModules, predefined, predefined2) where

import Control.Applicative (liftA2)
import Control.Arrow (first)
import Data.Coerce (coerce)
import Data.Either (partitionEithers)
import Data.Either.Validation (Validation(..), validationToEither)
import Data.Foldable (toList)
import Data.Functor.Identity (Identity(..))
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.List as List
import Data.Maybe (fromMaybe)
import Data.Map.Lazy (Map)
import qualified Data.Map.Lazy as Map
import Data.Semigroup (Semigroup(..), sconcat)
import qualified Data.Text as Text

import qualified Rank2
import qualified Rank2.TH
import qualified Transformation as Shallow
import qualified Transformation.Deep as Deep
import qualified Transformation.AG as AG
import qualified Transformation.Rank2
import Transformation.AG (Attribution(..), Atts, Inherited(..), Synthesized(..), Semantics)

import qualified Language.Oberon.AST as AST

import Debug.Trace

data Type = NominalType AST.QualIdent (Maybe Type)
          | RecordType{ancestry :: [AST.QualIdent],
                       recordFields :: Map AST.Ident Type}
          | NilType
          | IntegerType Int
          | StringType Int
          | ArrayType [Int] Type
          | PointerType Type
          | ReceiverType Type
          | ProcedureType Bool [(Bool, Type)] (Maybe Type)
          | UnknownType

data ErrorType = ArgumentCountMismatch Int Int
               | ExtraDimensionalIndex Int Int
               | IncomparableTypes Type Type
               | IncompatibleTypes Type Type
               | TooSmallArrayType Int Int
               | OpenArrayVariable
               | NonArrayType Type
               | NonBooleanType Type
               | NonFunctionType Type
               | NonIntegerType Type
               | NonNumericType Type
               | NonPointerType Type
               | NonProcedureType Type
               | NonRecordType Type
               | TypeMismatch Type Type
               | UnequalTypes Type Type
               | UnrealType Type
               | UnknownName AST.QualIdent
               | UnknownField AST.Ident Type
               deriving Show

type Error = (AST.Ident, Int, ErrorType)

instance Eq Type where
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

instance Show Type where
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

errorMessage :: ErrorType -> String
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

typeMessage :: Type -> String
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

nameMessage :: AST.QualIdent -> String
nameMessage (AST.QualIdent mod name) = Text.unpack mod <> "." <> Text.unpack name
nameMessage (AST.NonQualIdent name) = Text.unpack name

type Environment = Map AST.QualIdent Type

newtype Modules f' f = Modules (Map AST.Ident (f (AST.Module f' f')))

data TypeCheck = TypeCheck

data InhTCRoot = InhTCRoot{rootEnv :: Environment}

data InhTC = InhTC{env           :: Environment,
                   currentModule :: AST.Ident} deriving Show

data SynTC = SynTC{errors :: [Error]} deriving Show

data SynTC' = SynTC'{errors' :: [Error],
                     env' :: Environment} deriving Show

data SynTCMod = SynTCMod{moduleErrors :: [Error],
                         moduleEnv :: Environment,
                         pointerTargets :: Map AST.Ident AST.Ident} deriving Show

data SynTCType = SynTCType{typeErrors :: [Error],
                           typeName   :: Maybe AST.Ident,
                           definedType :: Type,
                           pointerTarget :: Maybe AST.Ident} deriving Show

data SynTCFields = SynTCFields{fieldErrors :: [Error],
                               fieldEnv :: Map AST.Ident Type} deriving Show

data SynTCHead = SynTCHead{headingErrors :: [Error],
                           insideEnv :: Environment,
                           outsideEnv :: Environment} deriving Show

data SynTCSig = SynTCSig{signatureErrors :: [Error],
                         signatureEnv :: Environment,
                         signatureType :: Type} deriving Show

data SynTCSec = SynTCSec{sectionErrors :: [Error],
                         sectionEnv :: Environment,
                         sectionParameters :: [(Bool, Type)]} deriving Show

data SynTCDes = SynTCDes{designatorErrors :: [Error],
                         designatorSelf   :: AST.Designator Identity Identity,
                         designatorType :: Type} deriving Show

data SynTCExp = SynTCExp{expressionErrors :: [Error],
                         inferredType :: Type} deriving Show

-- * Modules instances, TH candidates
instance (Functor p, Deep.Functor t AST.Module p q, Shallow.Functor t p q (AST.Module q q)) =>
         Deep.Functor t Modules p q where
   t <$> ~(Modules ms) = Modules (mapModule <$> ms)
      where mapModule m = t Shallow.<$> ((t Deep.<$>) <$> m)

instance Rank2.Functor (Modules f') where
   f <$> ~(Modules ms) = Modules (f <$> ms)

instance Rank2.Apply (Modules f') where
   ~(Modules fs) <*> ~(Modules ms) = Modules (Map.intersectionWith Rank2.apply fs ms)

-- * Boring attribute types
type instance Atts (Inherited TypeCheck) (Modules f' f) = InhTCRoot
type instance Atts (Synthesized TypeCheck) (Modules f' f) = SynTC
type instance Atts (Inherited TypeCheck) (AST.Module f' f) = InhTC
type instance Atts (Synthesized TypeCheck) (AST.Module f' f) = SynTCMod
type instance Atts (Inherited TypeCheck) (AST.Declaration f' f) = (InhTC, Map AST.Ident AST.Ident)
type instance Atts (Synthesized TypeCheck) (AST.Declaration f' f) = SynTCMod
type instance Atts (Inherited TypeCheck) (AST.ProcedureHeading f' f) = (InhTC, Map AST.Ident AST.Ident)
type instance Atts (Synthesized TypeCheck) (AST.ProcedureHeading f' f) = SynTCHead
type instance Atts (Inherited TypeCheck) (AST.FormalParameters f' f) = InhTC
type instance Atts (Synthesized TypeCheck) (AST.FormalParameters f' f) = SynTCSig
type instance Atts (Inherited TypeCheck) (AST.FPSection f' f) = InhTC
type instance Atts (Synthesized TypeCheck) (AST.FPSection f' f) = SynTCSec
type instance Atts (Inherited TypeCheck) (AST.Type f' f) = InhTC
type instance Atts (Synthesized TypeCheck) (AST.Type f' f) = SynTCType
type instance Atts (Inherited TypeCheck) (AST.FieldList f' f) = InhTC
type instance Atts (Synthesized TypeCheck) (AST.FieldList f' f) = SynTCFields
type instance Atts (Inherited TypeCheck) (AST.StatementSequence f' f) = InhTC
type instance Atts (Synthesized TypeCheck) (AST.StatementSequence f' f) = SynTC
type instance Atts (Inherited TypeCheck) (AST.Expression f' f) = InhTC
type instance Atts (Synthesized TypeCheck) (AST.Expression f' f) = SynTCExp
type instance Atts (Inherited TypeCheck) (AST.Element f' f) = InhTC
type instance Atts (Synthesized TypeCheck) (AST.Element f' f) = SynTCExp
type instance Atts (Inherited TypeCheck) (AST.Designator f' f) = InhTC
type instance Atts (Synthesized TypeCheck) (AST.Designator f' f) = SynTCDes
type instance Atts (Inherited TypeCheck) (Deep.Product AST.Expression AST.StatementSequence f' f) = InhTC
type instance Atts (Synthesized TypeCheck) (Deep.Product AST.Expression AST.StatementSequence f' f) = SynTC
type instance Atts (Inherited TypeCheck) (AST.Statement f' f) = InhTC
type instance Atts (Synthesized TypeCheck) (AST.Statement f' f) = SynTC
type instance Atts (Inherited TypeCheck) (AST.Case f' f) = (InhTC, Type)
type instance Atts (Synthesized TypeCheck) (AST.Case f' f) = SynTC
type instance Atts (Inherited TypeCheck) (AST.CaseLabels f' f) = (InhTC, Type)
type instance Atts (Synthesized TypeCheck) (AST.CaseLabels f' f) = SynTC
type instance Atts (Inherited TypeCheck) (AST.WithAlternative f' f) = InhTC
type instance Atts (Synthesized TypeCheck) (AST.WithAlternative f' f) = SynTC

-- * Rules

instance Attribution TypeCheck Modules (Int, Modules (Semantics TypeCheck) (Semantics TypeCheck)) where
   attribution TypeCheck (_, Modules self) (Inherited inheritance, Modules ms) =
     (Synthesized SynTC{errors= foldMap (moduleErrors . syn) ms},
      Modules (Map.mapWithKey moduleInheritance self))
     where moduleInheritance name mod = Inherited InhTC{env= rootEnv inheritance <> foldMap (moduleEnv . syn) ms,
                                                        currentModule= name}

instance Attribution TypeCheck AST.Module (Int, AST.Module (Semantics TypeCheck) (Semantics TypeCheck)) where
   attribution TypeCheck (pos, AST.Module moduleName imports decls body) 
               (Inherited inheritance, AST.Module _ _ decls' body') =
      (Synthesized SynTCMod{moduleErrors= foldMap (moduleErrors . syn) decls' <> foldMap (errors . syn) body',
                            moduleEnv= exportedEnv,
                            pointerTargets= pointers},
       AST.Module moduleName imports [Inherited (localEnv, pointers)] (Inherited localEnv <$ body))
      where exportedEnv = exportNominal <$> Map.mapKeysMonotonic export newEnv
            newEnv = Map.unionsWith mergeTypeBoundProcedures (moduleEnv . syn <$> decls')
            localEnv = InhTC (newEnv `Map.union` env inheritance) (currentModule inheritance)
            export (AST.NonQualIdent name) = AST.QualIdent moduleName name
            export q = q
            exportNominal (NominalType (AST.NonQualIdent name) (Just t)) =
              NominalType (AST.QualIdent moduleName name) (Just $ exportNominal' t)
            exportNominal t = exportNominal' t
            exportNominal' (RecordType ancestry fields) = RecordType (export <$> ancestry) (exportNominal' <$> fields)
            exportNominal' (ProcedureType False parameters result) =
              ProcedureType False ((exportNominal' <$>) <$> parameters) (exportNominal' <$> result)
            exportNominal' (PointerType target) = PointerType (exportNominal' target)
            exportNominal' (ArrayType dimensions itemType) = ArrayType dimensions (exportNominal' itemType)
            exportNominal' (NominalType q@(AST.NonQualIdent name) (Just t)) =
              fromMaybe (NominalType (AST.QualIdent moduleName name) $ Just $ exportNominal' t) (Map.lookup q exportedEnv)
            exportNominal' t = t
            pointers= foldMap (pointerTargets . syn) decls'
            mergeTypeBoundProcedures (NominalType (AST.NonQualIdent "") (Just t1)) t2 = mergeTypeBoundProcedures t1 t2
            mergeTypeBoundProcedures (NominalType q (Just t1)) t2 = NominalType q (Just $ mergeTypeBoundProcedures t1 t2)
            mergeTypeBoundProcedures t1 (NominalType (AST.NonQualIdent "") (Just t2)) = mergeTypeBoundProcedures t1 t2
            mergeTypeBoundProcedures t1 (NominalType q (Just t2)) = NominalType q (Just $ mergeTypeBoundProcedures t1 t2)
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

instance Attribution TypeCheck AST.Declaration (Int, AST.Declaration (Semantics TypeCheck) (Semantics TypeCheck)) where
   attribution TypeCheck (pos, AST.ConstantDeclaration namedef@(AST.IdentDef name _) _)
               (Inherited inheritance, AST.ConstantDeclaration _ expression) =
      (Synthesized SynTCMod{moduleErrors= expressionErrors (syn expression),
                            moduleEnv= Map.singleton (AST.NonQualIdent name) (inferredType $ syn expression),
                            pointerTargets= mempty},
       AST.ConstantDeclaration namedef (Inherited $ fst inheritance))
   attribution TypeCheck (pos, AST.TypeDeclaration namedef@(AST.IdentDef name _) _)
               (Inherited inheritance, AST.TypeDeclaration _ definition) =
      (Synthesized SynTCMod{moduleErrors= typeErrors (syn definition),
                            moduleEnv= Map.singleton qname (nominal $ definedType $ syn definition),
                            pointerTargets= foldMap (Map.singleton name) (pointerTarget $ syn definition)},
       AST.TypeDeclaration namedef (Inherited $ fst inheritance))
      where nominal t@NominalType{} = t
            nominal (PointerType t@RecordType{})
              | AST.NonQualIdent n <- qname =
                  NominalType qname (Just $ PointerType $ NominalType (AST.NonQualIdent $ n<>"^") (Just t))
            nominal t = NominalType qname (Just t)
            qname = AST.NonQualIdent name
   attribution TypeCheck (pos, AST.VariableDeclaration names _declaredType)
               (Inherited inheritance, AST.VariableDeclaration _names declaredType) =
      (Synthesized SynTCMod{moduleErrors= typeErrors (syn declaredType) 
                                          <> case definedType (syn declaredType)
                                             of ArrayType [] _ -> [(currentModule $ fst inheritance, pos, OpenArrayVariable)]
                                                _ -> [],
                            moduleEnv= foldMap (\name-> Map.singleton (AST.NonQualIdent $ defName name)
                                                        (definedType $ syn declaredType))
                                       names,
                            pointerTargets= mempty},
       AST.VariableDeclaration names (Inherited $ fst inheritance))
      where defName (AST.IdentDef name _) = name
   attribution TypeCheck (pos, AST.ProcedureDeclaration _heading _body)
               (Inherited inheritance,
                AST.ProcedureDeclaration heading body@(AST.ProcedureBody declarations statements)) =
      (Synthesized SynTCMod{moduleErrors= headingErrors (syn heading)
                                          <> foldMap (moduleErrors . syn) declarations
                                          <> foldMap (errors . syn) statements,
                            moduleEnv= outsideEnv (syn heading),
                            pointerTargets= mempty},
       AST.ProcedureDeclaration
          (Inherited inheritance)
          (AST.ProcedureBody [Inherited (localInherited, mempty)] (Just $ Inherited localInherited)))
      where localInherited = InhTC (foldMap (moduleEnv . syn) declarations <> env bodyInherited)
                                   (currentModule $ fst inheritance)
            bodyInherited = InhTC (insideEnv (syn heading) `Map.union` env (fst inheritance))
                                  (currentModule $ fst inheritance)
   attribution TypeCheck (pos, AST.ForwardDeclaration namedef@(AST.IdentDef name _) _signature)
               (Inherited inheritance, AST.ForwardDeclaration _namedef signature) =
      (Synthesized SynTCMod{moduleErrors= foldMap (signatureErrors . syn) signature,
                            moduleEnv= foldMap (Map.singleton (AST.NonQualIdent name) . signatureType . syn) signature,
                            pointerTargets= mempty},
       AST.ForwardDeclaration namedef (Just (Inherited $ fst inheritance)))

instance Attribution TypeCheck AST.ProcedureHeading (Int, AST.ProcedureHeading (Semantics TypeCheck) (Semantics TypeCheck)) where
   attribution TypeCheck (pos, AST.ProcedureHeading indirect namedef@(AST.IdentDef name _) _signature)
      (Inherited inheritance, AST.ProcedureHeading _indirect _ signature) =
      (Synthesized SynTCHead{headingErrors= foldMap (signatureErrors . syn) signature,
                             outsideEnv= Map.singleton (AST.NonQualIdent name) $
                                         maybe (ProcedureType False [] Nothing) (signatureType . syn) signature,
                             insideEnv= foldMap (signatureEnv . syn) signature},
       AST.ProcedureHeading indirect namedef (Just $ Inherited $ fst inheritance))
   attribution TypeCheck (pos, AST.TypeBoundHeading var receiverName receiverType indirect namedef@(AST.IdentDef name _) _signature)
      (Inherited inheritance, AST.TypeBoundHeading _var _name _type _indirect _ signature) =
      (Synthesized SynTCHead{headingErrors= receiverError <> foldMap (signatureErrors . syn) signature,
                             outsideEnv= case Map.lookup receiverType (snd inheritance)
                                         of Just targetName -> Map.singleton (AST.NonQualIdent targetName) methodType
                                            Nothing -> Map.singleton (AST.NonQualIdent receiverType) methodType,
                             insideEnv= receiverEnv `Map.union` foldMap (signatureEnv . syn) signature},
       AST.TypeBoundHeading var receiverName receiverType indirect namedef (Just $ Inherited $ fst inheritance))
      where receiverEnv =
               foldMap (Map.singleton (AST.NonQualIdent receiverName) . ReceiverType)
                       (Map.lookup (AST.NonQualIdent receiverType) $ env $ fst inheritance)
            methodType = NominalType (AST.NonQualIdent "") (Just $ RecordType [] $ Map.singleton name procedureType)
            procedureType = maybe (ProcedureType False [] Nothing) (signatureType . syn) signature
            receiverError =
               case Map.lookup (AST.NonQualIdent receiverType) (env $ fst inheritance)
               of Nothing -> [(currentModule $ fst inheritance, pos, UnknownName $ AST.NonQualIdent receiverType)]
                  Just t 
                     | RecordType{} <- ultimate t -> []
                     | PointerType t' <- ultimate t, RecordType{} <- ultimate t' -> []
                     | otherwise -> [(currentModule $ fst inheritance, pos, NonRecordType t)]

instance Attribution TypeCheck AST.FormalParameters (Int, AST.FormalParameters (Semantics TypeCheck) (Semantics TypeCheck)) where
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

instance Attribution TypeCheck AST.FPSection (Int, AST.FPSection (Semantics TypeCheck) (Semantics TypeCheck)) where
   attribution TypeCheck (pos, AST.FPSection var names _typeDef) (Inherited inheritance, AST.FPSection _var _names typeDef) =
      (Synthesized SynTCSec{sectionErrors= typeErrors (syn typeDef),
                            sectionParameters= (var, definedType (syn typeDef)) <$ toList names,
                            sectionEnv= Map.fromList (toList
                                                      $ flip (,) (definedType $ syn typeDef) . AST.NonQualIdent 
                                                      <$> names)},
       AST.FPSection var names (Inherited inheritance))

instance Attribution TypeCheck AST.Type (Int, AST.Type (Semantics TypeCheck) (Semantics TypeCheck)) where
   attribution TypeCheck (pos, AST.TypeReference q) (Inherited inheritance, _) = 
      (Synthesized SynTCType{typeErrors= if Map.member q (env inheritance) then []
                                         else [(currentModule inheritance, pos, UnknownName q)],
                             typeName= case q 
                                       of AST.NonQualIdent name -> Just name
                                          _ -> Nothing,
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

instance Attribution TypeCheck AST.FieldList (Int, AST.FieldList (Semantics TypeCheck) (Semantics TypeCheck)) where
   attribution TypeCheck (pos, AST.FieldList names _declaredType) (Inherited inheritance, AST.FieldList _names declaredType) =
      (Synthesized SynTCFields{fieldErrors= typeErrors (syn declaredType),
                               fieldEnv= foldMap (\name-> Map.singleton (defName name) (definedType $ syn declaredType)) 
                                         names},
       AST.FieldList names (Inherited inheritance))
      where defName (AST.IdentDef name _) = name
   attribution TypeCheck self (Inherited inheritance, AST.EmptyFieldList) =
     (Synthesized SynTCFields{fieldErrors= [], fieldEnv= mempty},
      AST.EmptyFieldList)

instance Attribution TypeCheck (Deep.Product AST.Expression AST.StatementSequence) (Int, (Deep.Product AST.Expression AST.StatementSequence) (Semantics TypeCheck) (Semantics TypeCheck)) where
   attribution TypeCheck (pos, _) (Inherited inheritance, Deep.Pair condition statements) =
      (Synthesized SynTC{errors= booleanExpressionErrors inheritance pos (syn condition) <> errors (syn statements)},
       Deep.Pair (Inherited inheritance) (Inherited inheritance))

instance Attribution TypeCheck AST.StatementSequence (Int, AST.StatementSequence (Semantics TypeCheck) (Semantics TypeCheck)) where
   attribution TypeCheck (pos, AST.StatementSequence statements) (Inherited inheritance, AST.StatementSequence statements') =
      (Synthesized SynTC{errors= foldMap (errors . syn) statements'},
       AST.StatementSequence (pure $ Inherited inheritance))

instance Attribution TypeCheck AST.Statement (Int, AST.Statement (Semantics TypeCheck) (Semantics TypeCheck)) where
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
                    && designatorSelf (syn procedure') == AST.Variable (AST.NonQualIdent "ASSERT")
                    || length formalTypes == 1 && (length <$> parameters) == Just 2
                    && designatorSelf (syn procedure') == AST.Variable (AST.NonQualIdent "NEW")
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
                        InhTC (Map.insert (AST.NonQualIdent counter) (NominalType (AST.NonQualIdent "INTEGER") Nothing)
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

instance Attribution TypeCheck AST.WithAlternative (Int, AST.WithAlternative (Semantics TypeCheck) (Semantics TypeCheck)) where
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

instance Attribution TypeCheck AST.Case (Int, AST.Case (Semantics TypeCheck) (Semantics TypeCheck)) where
   attribution TypeCheck self (Inherited inheritance, AST.Case labels body) =
      (Synthesized SynTC{errors= foldMap (errors . syn) labels <> errors (syn body)},
       AST.Case (pure $ Inherited inheritance) (Inherited $ fst inheritance))
   attribution TypeCheck self (Inherited inheritance, AST.EmptyCase) = (Synthesized SynTC{errors= []}, AST.EmptyCase)

instance Attribution TypeCheck AST.CaseLabels (Int, AST.CaseLabels (Semantics TypeCheck) (Semantics TypeCheck)) where
   attribution TypeCheck (pos, _) (Inherited inheritance, AST.SingleLabel value) =
      (Synthesized SynTC{errors= assignmentCompatible (fst inheritance) pos (snd inheritance) (inferredType $ syn value)},
       AST.SingleLabel (Inherited $ fst inheritance))
   attribution TypeCheck (pos, _) (Inherited (inheritance, caseType), AST.LabelRange start end) =
      (Synthesized SynTC{errors= assignmentCompatible inheritance pos caseType (inferredType $ syn start)
                                 <> assignmentCompatible inheritance pos caseType (inferredType $ syn end)},
       AST.LabelRange (Inherited inheritance) (Inherited inheritance))

instance Attribution TypeCheck AST.Expression (Int, AST.Expression (Semantics TypeCheck) (Semantics TypeCheck)) where
   attribution TypeCheck (pos, AST.Relation op _ _) (Inherited inheritance, AST.Relation _op left right) =
      (Synthesized SynTCExp{expressionErrors= case expressionErrors (syn left) <> expressionErrors (syn right)
                                              of [] | t1 == t2 -> []
                                                    | AST.Is <- op -> assignmentCompatible inheritance pos t1 t2
                                                    | AST.In <- op -> membershipCompatible (ultimate t1) (ultimate t2)
                                                    | equality op, [] <- assignmentCompatible inheritance pos t1 t2 -> []
                                                    | equality op, [] <- assignmentCompatible inheritance pos t2 t1 -> []
                                                    | op /= AST.Is -> comparable (ultimate t1) (ultimate t2)
                                                    | otherwise -> [(currentModule inheritance, pos, TypeMismatch t1 t2)]
                                                 errs -> errs,
                            inferredType= NominalType (AST.NonQualIdent "BOOLEAN") Nothing},
       AST.Relation op (Inherited inheritance) (Inherited inheritance))
      where t1 = inferredType (syn left)
            t2 = inferredType (syn right)
            equality AST.Equal = True
            equality AST.Unequal = True
            equality _ = False
            comparable (NominalType (AST.NonQualIdent "BOOLEAN") Nothing)
                       (NominalType (AST.NonQualIdent "BOOLEAN") Nothing) = []
            comparable (NominalType (AST.NonQualIdent "CHAR") Nothing)
                       (NominalType (AST.NonQualIdent "CHAR") Nothing) = []
            comparable StringType{} StringType{} = []
            comparable (StringType 1) (NominalType (AST.NonQualIdent "CHAR") Nothing) = []
            comparable (NominalType (AST.NonQualIdent "CHAR") Nothing) (StringType 1) = []
            comparable StringType{} (ArrayType _ (NominalType (AST.NonQualIdent "CHAR") Nothing)) = []
            comparable (ArrayType _ (NominalType (AST.NonQualIdent "CHAR") Nothing)) StringType{} = []
            comparable (ArrayType _ (NominalType (AST.NonQualIdent "CHAR") Nothing))
                       (ArrayType _ (NominalType (AST.NonQualIdent "CHAR") Nothing)) = []
            comparable (NominalType (AST.NonQualIdent t1) Nothing)
                       (NominalType (AST.NonQualIdent t2) Nothing) | isNumerical t1 && isNumerical t2 = []
            comparable (NominalType (AST.NonQualIdent t1) Nothing) IntegerType{} | isNumerical t1 = []
            comparable IntegerType{} (NominalType (AST.NonQualIdent t2) Nothing) | isNumerical t2 = []
            comparable t1 t2 = [(currentModule inheritance, pos, IncomparableTypes t1 t2)]
            membershipCompatible IntegerType{} (NominalType (AST.NonQualIdent "SET") Nothing) = []
            membershipCompatible (NominalType (AST.NonQualIdent t) Nothing)
                                 (NominalType (AST.NonQualIdent "SET") Nothing) | isNumerical t = []
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
                            inferredType= NominalType (AST.NonQualIdent "BOOLEAN") Nothing},
       AST.Or (Inherited inheritance) (Inherited inheritance))
   attribution TypeCheck (pos, _) (Inherited inheritance, AST.Multiply left right) =
      (Synthesized SynTCExp{expressionErrors= binarySetOrNumericOperatorErrors inheritance pos (syn left) (syn right),
                            inferredType= binaryNumericOperatorType div (syn left) (syn right)},
       AST.Multiply (Inherited inheritance) (Inherited inheritance))
   attribution TypeCheck (pos, _) (Inherited inheritance, AST.Divide left right) =
      (Synthesized SynTCExp{expressionErrors=
                               case (syn left, syn right)
                               of (SynTCExp{expressionErrors= [],
                                            inferredType= NominalType (AST.NonQualIdent "REAL") Nothing},
                                   SynTCExp{expressionErrors= [],
                                            inferredType= NominalType (AST.NonQualIdent "REAL") Nothing}) -> []
                                  (SynTCExp{expressionErrors= [],
                                            inferredType= NominalType (AST.NonQualIdent "SET") Nothing},
                                   SynTCExp{expressionErrors= [],
                                            inferredType= NominalType (AST.NonQualIdent "SET") Nothing}) -> []
                                  (SynTCExp{expressionErrors= [], inferredType= t1},
                                   SynTCExp{expressionErrors= [], inferredType= t2})
                                    | t1 == t2 -> [(currentModule inheritance, pos, UnrealType t1)]
                                    | otherwise -> [(currentModule inheritance, pos, TypeMismatch t1 t2)],
                            inferredType= NominalType (AST.NonQualIdent "REAL") Nothing},
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
                            inferredType= NominalType (AST.NonQualIdent "BOOLEAN") Nothing},
       AST.And (Inherited inheritance) (Inherited inheritance))
   attribution TypeCheck (pos, AST.Integer x) (Inherited inheritance, _) =
      (Synthesized SynTCExp{expressionErrors= mempty,
                            inferredType= IntegerType (read $ Text.unpack x)},
       AST.Integer x)
   attribution TypeCheck self (Inherited inheritance, AST.Real x) =
      (Synthesized SynTCExp{expressionErrors= mempty,
                            inferredType= NominalType (AST.NonQualIdent "REAL") Nothing},
       AST.Real x)
   attribution TypeCheck self (Inherited inheritance, AST.CharConstant x) =
      (Synthesized SynTCExp{expressionErrors= mempty,
                            inferredType= NominalType (AST.NonQualIdent "CHAR") Nothing},
       AST.CharConstant x)
   attribution TypeCheck self (Inherited inheritance, AST.CharCode x) =
      (Synthesized SynTCExp{expressionErrors= mempty,
                            inferredType= NominalType (AST.NonQualIdent "CHAR") Nothing},
       AST.CharCode x)
   attribution TypeCheck (pos, AST.String x) (Inherited inheritance, _) =
      (Synthesized SynTCExp{expressionErrors= mempty,
                            inferredType= StringType (Text.length x)},
       AST.String x)
   attribution TypeCheck self (Inherited inheritance, AST.Nil) =
      (Synthesized SynTCExp{expressionErrors= mempty,
                            inferredType= NilType},
       AST.Nil)
   attribution TypeCheck self (Inherited inheritance, AST.Set elements) =
      (Synthesized SynTCExp{expressionErrors= mempty,
                            inferredType= NominalType (AST.NonQualIdent "SET") Nothing},
       AST.Set [Inherited inheritance])
   attribution TypeCheck self (Inherited inheritance, AST.Read designator) =
      (Synthesized SynTCExp{expressionErrors= designatorErrors (syn designator),
                            inferredType= designatorType (syn designator)},
       AST.Read (Inherited inheritance))
   attribution TypeCheck (pos, AST.FunctionCall _designator parameters)
               (Inherited inheritance, AST.FunctionCall designator parameters') =
      (Synthesized SynTCExp{expressionErrors= case {-# SCC "FunctionCall" #-} syn designator
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
                            inferredType= case syn designator
                                          of SynTCDes{designatorSelf= AST.Variable (AST.QualIdent "SYSTEM" name)}
                                               | Just t <- systemCallType name (inferredType . syn <$> parameters') -> t
                                             SynTCDes{designatorSelf= d,
                                                      designatorType= t}
                                               | ProcedureType _ _ (Just returnType) <- ultimate t ->
                                                   case returnType
                                                   of UnknownType -> builtinType d (inferredType . syn <$> parameters')
                                                      _ -> returnType
                                             _ -> UnknownType},
       AST.FunctionCall (Inherited inheritance) [Inherited inheritance])
     where builtinType (AST.Variable (AST.NonQualIdent "MAX")) [t@(NominalType (AST.NonQualIdent name) Nothing)] =
             case name
             of "SET" -> IntegerType 63
                "SHORTINT" -> IntegerType (2^15-1)
                "INTEGER" -> IntegerType (2^31-1)
                "LONGINT" -> IntegerType (2^63-1)
                _ -> t
           builtinType (AST.Variable (AST.NonQualIdent "MIN")) [t@(NominalType (AST.NonQualIdent name) Nothing)] =
             case name
             of "SET" -> IntegerType 0
                "SHORTINT" -> IntegerType (-2^15)
                "INTEGER" -> IntegerType (-2^31)
                "LONGINT" -> IntegerType (-2^63)
                _ -> t
           systemCallType "VAL" [t1, t2] = Just t1
           systemCallType _ _ = Nothing
   attribution TypeCheck (pos, _) (Inherited inheritance, AST.Not expr) =
      (Synthesized SynTCExp{expressionErrors= booleanExpressionErrors inheritance pos (syn expr),
                            inferredType= NominalType (AST.NonQualIdent "BOOLEAN") Nothing},
       AST.Not (Inherited inheritance))

instance Attribution TypeCheck AST.Element (Int, AST.Element (Semantics TypeCheck) (Semantics TypeCheck)) where
   attribution TypeCheck (pos, _) (Inherited inheritance, AST.Element expr) =
      (Synthesized SynTCExp{expressionErrors= integerExpressionErrors inheritance pos (syn expr),
                            inferredType= NominalType (AST.NonQualIdent "SET") Nothing},
       AST.Element (Inherited inheritance))
   attribution TypeCheck (pos, _) (Inherited inheritance, AST.Range low high) =
      (Synthesized SynTCExp{expressionErrors= integerExpressionErrors inheritance pos (syn low)
                                              <> integerExpressionErrors inheritance pos (syn high),
                            inferredType= NominalType (AST.NonQualIdent "SET") Nothing},
       AST.Range (Inherited inheritance) (Inherited inheritance))

instance Attribution TypeCheck AST.Designator (Int, AST.Designator (Semantics TypeCheck) (Semantics TypeCheck)) where
   attribution TypeCheck (pos, AST.Variable q) (Inherited inheritance, _) =
      (Synthesized SynTCDes{designatorErrors= case designatorType
                                              of Nothing -> [(currentModule inheritance, pos, UnknownName q)]
                                                 Just{} -> [],
                            designatorSelf= AST.Variable q,
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
                            designatorSelf= AST.Field (Identity $ designatorSelf $ syn record) fieldName,
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

unaryNumericOperatorErrors :: InhTC -> Int -> SynTCExp -> [Error]
unaryNumericOperatorErrors _ _ SynTCExp{expressionErrors= [], inferredType= IntegerType{}} = []
unaryNumericOperatorErrors _ _ SynTCExp{expressionErrors= [],
                                        inferredType= NominalType (AST.NonQualIdent name) Nothing}
  | isNumerical name = []
unaryNumericOperatorErrors inheritance pos SynTCExp{expressionErrors= [], inferredType= t} = 
   [(currentModule inheritance, pos, NonNumericType t)]
unaryNumericOperatorErrors _ _ SynTCExp{expressionErrors= errs} = errs

unaryNumericOperatorType :: (Int -> Int) -> SynTCExp -> Type
unaryNumericOperatorType f SynTCExp{inferredType= IntegerType x} = IntegerType (f x)
unaryNumericOperatorType _ SynTCExp{inferredType= t} = t

binarySetOrNumericOperatorErrors :: InhTC -> Int -> SynTCExp -> SynTCExp -> [Error]
binarySetOrNumericOperatorErrors _ _
  SynTCExp{expressionErrors= [], inferredType= NominalType (AST.NonQualIdent name1) Nothing}
  SynTCExp{expressionErrors= [], inferredType= NominalType (AST.NonQualIdent name2) Nothing}
  | isNumerical name1, isNumerical name2 = []
  | name1 == "SET", name2 == "SET" = []
binarySetOrNumericOperatorErrors _ _
  SynTCExp{expressionErrors= [], inferredType= IntegerType{}}
  SynTCExp{expressionErrors= [], inferredType= NominalType (AST.NonQualIdent name) Nothing}
  | isNumerical name = []
binarySetOrNumericOperatorErrors _ _
  SynTCExp{expressionErrors= [], inferredType= NominalType (AST.NonQualIdent name) Nothing}
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

binaryNumericOperatorType :: (Int -> Int -> Int) -> SynTCExp -> SynTCExp -> Type
binaryNumericOperatorType f SynTCExp{inferredType= IntegerType x} SynTCExp{inferredType= IntegerType y} =
  IntegerType (f x y)
binaryNumericOperatorType _ SynTCExp{inferredType= t1} SynTCExp{inferredType= t2}
  | t1 == t2 = t1
  | IntegerType{} <- t1 = t2
  | IntegerType{} <- t2 = t1
  | NominalType (AST.NonQualIdent name1) Nothing <- t1,
    NominalType (AST.NonQualIdent name2) Nothing <- t2,
    Just index1 <- List.elemIndex name1 numericTypeNames,
    Just index2 <- List.elemIndex name2 numericTypeNames =
      NominalType (AST.NonQualIdent $ numericTypeNames !! max index1 index2) Nothing
  | otherwise = t1

binaryIntegerOperatorErrors :: InhTC -> Int ->  SynTCExp -> SynTCExp -> [Error]
binaryIntegerOperatorErrors inheritance pos syn1 syn2 = integerExpressionErrors inheritance pos syn1 
                                                      <> integerExpressionErrors inheritance pos syn2

integerExpressionErrors inheritance pos SynTCExp{expressionErrors= [], inferredType= t}
  | isIntegerType t = []
  | otherwise = [(currentModule inheritance, pos, NonIntegerType t)]
integerExpressionErrors _ _ SynTCExp{expressionErrors= errs} = errs

isIntegerType IntegerType{} = True
isIntegerType (NominalType (AST.NonQualIdent "SHORTINT") Nothing) = True
isIntegerType (NominalType (AST.NonQualIdent "INTEGER") Nothing) = True
isIntegerType (NominalType (AST.NonQualIdent "LONGINT") Nothing) = True
isIntegerType t = False

booleanExpressionErrors _ _ SynTCExp{expressionErrors= [],
                                   inferredType= NominalType (AST.NonQualIdent "BOOLEAN") Nothing} = []
booleanExpressionErrors inheritance pos SynTCExp{expressionErrors= [], inferredType= t} = 
   [(currentModule inheritance, pos, NonBooleanType t)]
booleanExpressionErrors _ _ SynTCExp{expressionErrors= errs} = errs

binaryBooleanOperatorErrors :: InhTC -> Int -> SynTCExp -> SynTCExp -> [Error]
binaryBooleanOperatorErrors _inh _pos
  SynTCExp{expressionErrors= [], inferredType= NominalType (AST.NonQualIdent "BOOLEAN") Nothing}
  SynTCExp{expressionErrors= [], inferredType= NominalType (AST.NonQualIdent "BOOLEAN") Nothing} = []
binaryBooleanOperatorErrors inheritance pos
  SynTCExp{expressionErrors= [], inferredType= t1}
  SynTCExp{expressionErrors= [], inferredType= t2}
  | t1 == t2 = [(currentModule inheritance, pos, NonBooleanType t1)]
  | otherwise = [(currentModule inheritance, pos, TypeMismatch t1 t2)]
binaryBooleanOperatorErrors _ _ SynTCExp{expressionErrors= errs1} SynTCExp{expressionErrors= errs2} = errs1 <> errs2

parameterCompatible :: InhTC -> Int -> (Bool, Type) -> Type -> [Error]
parameterCompatible _ _ (_, expected@(ArrayType [] _)) actual
  | arrayCompatible expected actual = []
parameterCompatible inheritance pos (True, expected) actual
  | expected == actual = []
  | otherwise = [(currentModule inheritance, pos, UnequalTypes expected actual)]
parameterCompatible inheritance pos (False, expected) actual
  | NominalType (AST.NonQualIdent "ARRAY") Nothing <- expected, ArrayType{} <- actual = []
  | otherwise = assignmentCompatible inheritance pos expected actual

assignmentCompatible :: InhTC -> Int -> Type -> Type -> [Error]
assignmentCompatible inheritance pos expected actual
   | expected == actual = []
   | NominalType (AST.NonQualIdent name1) Nothing <- expected,
     NominalType (AST.NonQualIdent name2) Nothing <- actual,
     Just index1 <- List.elemIndex name1 numericTypeNames,
     Just index2 <- List.elemIndex name2 numericTypeNames, 
     index1 >= index2 = []
   | NominalType (AST.NonQualIdent name) Nothing <- expected,
     IntegerType{} <- actual, isNumerical name = []
   | expected == NominalType (AST.NonQualIdent "BASIC TYPE") Nothing,
     NominalType (AST.NonQualIdent q) Nothing <- actual,
     q `elem` ["BOOLEAN", "CHAR", "SHORTINT", "INTEGER", "LONGINT", "REAL", "LONGREAL", "SET"] = []
   | expected == NominalType (AST.NonQualIdent "POINTER") Nothing, PointerType{} <- actual = []
   | expected == NominalType (AST.NonQualIdent "POINTER") Nothing, NominalType _ (Just t) <- actual =
       assignmentCompatible inheritance pos expected t
   | expected == NominalType (AST.NonQualIdent "CHAR") Nothing, actual == StringType 1 = []
   | ReceiverType t <- actual = assignmentCompatible inheritance pos expected t
   | ReceiverType t <- expected = assignmentCompatible inheritance pos t actual
   | NilType <- actual, PointerType{} <- expected = []
   | NilType <- actual, ProcedureType{} <- expected = []
   | NilType <- actual, NominalType _ (Just t) <- expected = assignmentCompatible inheritance pos t actual
--   | ArrayType [] (NominalType (AST.NonQualIdent "CHAR") Nothing) <- expected, StringType{} <- actual = []
   | ArrayType [m] (NominalType (AST.NonQualIdent "CHAR") Nothing) <- expected, StringType n <- actual = 
      if m < n then [(currentModule inheritance, pos, TooSmallArrayType m n)] else []
   | targetExtends actual expected = []
   | NominalType _ (Just t) <- expected, ProcedureType{} <- actual = assignmentCompatible inheritance pos t actual
   | otherwise = [(currentModule inheritance, pos, IncompatibleTypes expected actual)]

arrayCompatible (ArrayType [] t1) (ArrayType _ t2) = t1 == t2 || arrayCompatible t1 t2
arrayCompatible (ArrayType [] (NominalType (AST.NonQualIdent "CHAR") Nothing)) StringType{} = True
arrayCompatible (NominalType _ (Just t1)) t2 = arrayCompatible t1 t2
arrayCompatible t1 (NominalType _ (Just t2)) = arrayCompatible t1 t2
arrayCompatible _ _ = False

extends, targetExtends :: Type -> Type -> Bool
t1 `extends` t2 | t1 == t2 = True
RecordType ancestry _ `extends` NominalType q _ = q `elem` ancestry
NominalType _ (Just t1) `extends` t2 = t1 `extends` t2
t1 `extends` t2 = False -- error (show (t1, t2))

ultimate :: Type -> Type
ultimate (NominalType _ (Just t)) = ultimate t
ultimate t = t

isNumerical t = t `elem` numericTypeNames
numericTypeNames = ["SHORTINT", "INTEGER", "LONGINT", "REAL", "LONGREAL"]

PointerType t1 `targetExtends` PointerType t2 = t1 `extends` t2
NominalType _ (Just t1) `targetExtends` t2 = t1 `targetExtends` t2
t1 `targetExtends` NominalType _ (Just t2) = t1 `targetExtends` t2
t1 `targetExtends` t2 | t1 == t2 = True
t1 `targetExtends` t2 = False

-- * More boring Shallow.Functor instances, TH candidates
instance Shallow.Functor TypeCheck Placed (Semantics TypeCheck)
         (Modules (Semantics TypeCheck) (Semantics TypeCheck)) where
   (<$>) = AG.mapDefault id snd
instance Shallow.Functor TypeCheck Placed (Semantics TypeCheck)
         (AST.Module (Semantics TypeCheck) (Semantics TypeCheck)) where
   (<$>) = AG.mapDefault id snd
instance Shallow.Functor TypeCheck Placed (Semantics TypeCheck)
         (AST.Declaration (Semantics TypeCheck) (Semantics TypeCheck)) where
   (<$>) = AG.mapDefault id snd
instance Shallow.Functor TypeCheck Placed (Semantics TypeCheck)
         (AST.ProcedureHeading (Semantics TypeCheck) (Semantics TypeCheck)) where
   (<$>) = AG.mapDefault id snd
instance Shallow.Functor TypeCheck Placed (Semantics TypeCheck)
         (AST.FormalParameters (Semantics TypeCheck) (Semantics TypeCheck)) where
   (<$>) = AG.mapDefault id snd
instance Shallow.Functor TypeCheck Placed (Semantics TypeCheck)
         (AST.FPSection (Semantics TypeCheck) (Semantics TypeCheck)) where
   (<$>) = AG.mapDefault id snd
instance Shallow.Functor TypeCheck Placed (Semantics TypeCheck)
         (Deep.Product AST.Expression AST.StatementSequence (Semantics TypeCheck) (Semantics TypeCheck)) where
   (<$>) = AG.mapDefault id snd
instance Shallow.Functor TypeCheck Placed (Semantics TypeCheck)
         (AST.StatementSequence (Semantics TypeCheck) (Semantics TypeCheck)) where
   (<$>) = AG.mapDefault id snd
instance Shallow.Functor TypeCheck Placed (Semantics TypeCheck)
         (AST.Statement (Semantics TypeCheck) (Semantics TypeCheck)) where
   (<$>) = AG.mapDefault id snd
instance Shallow.Functor TypeCheck Placed (Semantics TypeCheck)
         (AST.Case (Semantics TypeCheck) (Semantics TypeCheck)) where
   (<$>) = AG.mapDefault id snd
instance Shallow.Functor TypeCheck Placed (Semantics TypeCheck)
         (AST.CaseLabels (Semantics TypeCheck) (Semantics TypeCheck)) where
   (<$>) = AG.mapDefault id snd
instance Shallow.Functor TypeCheck Placed (Semantics TypeCheck)
         (AST.WithAlternative (Semantics TypeCheck) (Semantics TypeCheck)) where
   (<$>) = AG.mapDefault id snd
instance Shallow.Functor TypeCheck Placed (Semantics TypeCheck)
         (AST.Expression (Semantics TypeCheck) (Semantics TypeCheck)) where
   (<$>) = AG.mapDefault id snd
instance Shallow.Functor TypeCheck Placed (Semantics TypeCheck)
         (AST.Element (Semantics TypeCheck) (Semantics TypeCheck)) where
   (<$>) = AG.mapDefault id snd
instance Shallow.Functor TypeCheck Placed (Semantics TypeCheck)
         (AST.Designator (Semantics TypeCheck) (Semantics TypeCheck)) where
   (<$>) = AG.mapDefault id snd
instance Shallow.Functor TypeCheck Placed (Semantics TypeCheck)
         (AST.Type (Semantics TypeCheck) (Semantics TypeCheck)) where
   (<$>) = AG.mapDefault id snd
instance Shallow.Functor TypeCheck Placed (Semantics TypeCheck)
         (AST.FieldList (Semantics TypeCheck) (Semantics TypeCheck)) where
   (<$>) = AG.mapDefault id snd

-- * Unsafe Rank2 AST instances

instance Rank2.Apply (AST.Module f') where
   AST.Module name1 imports1 decls1 body1 <*> ~(AST.Module name2 imports2 decls2 body2) =
      AST.Module name1 imports1 (liftA2 Rank2.apply decls1 decls2) (liftA2 Rank2.apply body1 body2)

type Placed = ((,) Int)

checkModules :: Environment -> Map AST.Ident (AST.Module Placed Placed) -> [Error]
checkModules predef modules =
   errors (syn (TypeCheck Shallow.<$> (0, TypeCheck Deep.<$> Modules modules')
                `Rank2.apply`
                Inherited (InhTCRoot predef)))
   where modules' = ((,) 0) <$> modules

predefined, predefined2 :: Environment
-- | The set of 'Predefined' types and procedures defined in the Oberon Language Report.
predefined = Map.fromList $ map (first AST.NonQualIdent) $
   [("BOOLEAN", NominalType (AST.NonQualIdent "BOOLEAN") Nothing),
    ("CHAR", NominalType (AST.NonQualIdent "CHAR") Nothing),
    ("SHORTINT", NominalType (AST.NonQualIdent "SHORTINT") Nothing),
    ("INTEGER", NominalType (AST.NonQualIdent "INTEGER") Nothing),
    ("LONGINT", NominalType (AST.NonQualIdent "LONGINT") Nothing),
    ("REAL", NominalType (AST.NonQualIdent "REAL") Nothing),
    ("LONGREAL", NominalType (AST.NonQualIdent "LONGREAL") Nothing),
    ("SET", NominalType (AST.NonQualIdent "SET") Nothing),
    ("TRUE", NominalType (AST.NonQualIdent "BOOLEAN") Nothing),
    ("FALSE", NominalType (AST.NonQualIdent "BOOLEAN") Nothing),
    ("ABS", ProcedureType False [(False, NominalType (AST.NonQualIdent "INTEGER") Nothing)] $
            Just $ NominalType (AST.NonQualIdent "INTEGER") Nothing),
    ("ASH", ProcedureType False [(False, NominalType (AST.NonQualIdent "INTEGER") Nothing)] $
            Just $ NominalType (AST.NonQualIdent "INTEGER") Nothing),
    ("CAP", ProcedureType False [(False, NominalType (AST.NonQualIdent "CHAR") Nothing)] $
            Just $ NominalType (AST.NonQualIdent "CHAR") Nothing),
    ("LEN", ProcedureType False [(False, NominalType (AST.NonQualIdent "ARRAY") Nothing)] $
            Just $ NominalType (AST.NonQualIdent "LONGINT") Nothing),
    ("MAX", ProcedureType False [(False, NominalType (AST.NonQualIdent "BASIC TYPE") Nothing)] $ Just UnknownType),
    ("MIN", ProcedureType False [(False, NominalType (AST.NonQualIdent "BASIC TYPE") Nothing)] $ Just UnknownType),
    ("ODD", ProcedureType False [(False, NominalType (AST.NonQualIdent "CHAR") Nothing)] $
            Just $ NominalType (AST.NonQualIdent "BOOLEAN") Nothing),
    ("SIZE", ProcedureType False [(False, NominalType (AST.NonQualIdent "CHAR") Nothing)] $
             Just $ NominalType (AST.NonQualIdent "INTEGER") Nothing),
    ("ORD", ProcedureType False [(False, NominalType (AST.NonQualIdent "CHAR") Nothing)] $
            Just $ NominalType (AST.NonQualIdent "INTEGER") Nothing),
    ("CHR", ProcedureType False [(False, NominalType (AST.NonQualIdent "INTEGER") Nothing)] $
            Just $ NominalType (AST.NonQualIdent "CHAR") Nothing),
    ("SHORT", ProcedureType False [(False, NominalType (AST.NonQualIdent "INTEGER") Nothing)]
              $ Just $ NominalType (AST.NonQualIdent "INTEGER") Nothing),
    ("LONG", ProcedureType False [(False, NominalType (AST.NonQualIdent "INTEGER") Nothing)] $
             Just $ NominalType (AST.NonQualIdent "INTEGER") Nothing),
    ("ENTIER", ProcedureType False [(False, NominalType (AST.NonQualIdent "REAL") Nothing)] $
               Just $ NominalType (AST.NonQualIdent "INTEGER") Nothing),
    ("INC", ProcedureType False [(False, NominalType (AST.NonQualIdent "LONGINT") Nothing)] Nothing),
    ("DEC", ProcedureType False [(False, NominalType (AST.NonQualIdent "LONGINT") Nothing)] Nothing),
    ("INCL", ProcedureType False [(False, NominalType (AST.NonQualIdent "SET") Nothing),
                                  (False, NominalType (AST.NonQualIdent "INTEGER") Nothing)] Nothing),
    ("EXCL", ProcedureType False [(False, NominalType (AST.NonQualIdent "SET") Nothing),
                                  (False, NominalType (AST.NonQualIdent "INTEGER") Nothing)] Nothing),
    ("COPY", ProcedureType False [(False, NominalType (AST.NonQualIdent "ARRAY") Nothing),
                                  (False, NominalType (AST.NonQualIdent "ARRAY") Nothing)] Nothing),
    ("NEW", ProcedureType False [(False, NominalType (AST.NonQualIdent "POINTER") Nothing)] Nothing),
    ("HALT", ProcedureType False [(False, NominalType (AST.NonQualIdent "INTEGER") Nothing)] Nothing)]

-- | The set of 'Predefined' types and procedures defined in the Oberon-2 Language Report.
predefined2 = predefined <>
   Map.fromList (first AST.NonQualIdent <$>
                 [("ASSERT", ProcedureType False [(False, NominalType (AST.NonQualIdent "BOOLEAN") Nothing),
                                                  (False, NominalType (AST.NonQualIdent "INTEGER") Nothing)] Nothing)])

$(mconcat <$> mapM Rank2.TH.unsafeDeriveApply
  [''AST.Declaration, ''AST.Type, ''AST.Expression,
   ''AST.Element, ''AST.Designator, ''AST.FieldList,
   ''AST.ProcedureHeading, ''AST.FormalParameters, ''AST.FPSection, ''AST.ProcedureBody,
   ''AST.Statement, ''AST.StatementSequence, ''AST.WithAlternative, ''AST.Case, ''AST.CaseLabels])
