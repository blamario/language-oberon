{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, OverloadedStrings,
             TemplateHaskell, TypeFamilies, UndecidableInstances #-}

module Language.Oberon.TypeChecker (Error(..), checkModules, predefined, predefined2) where

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
               | DuplicateBinding AST.Ident
               | ExtraDimensionalIndex Type
               | IncomparableTypes Type Type
               | IncompatibleTypes Type Type
               | TooSmallArrayType Type
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

type Error = (Int, ErrorType)

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

type Environment = Map AST.QualIdent Type

newtype Modules f' f = Modules (Map AST.Ident (f (AST.Module f' f')))

data TypeCheck = TypeCheck

data InhTC = InhTC{env :: Environment} deriving Show

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
type instance Atts (Inherited TypeCheck) (Modules f' f) = InhTC
type instance Atts (Synthesized TypeCheck) (Modules f' f) = SynTC
type instance Atts (Inherited TypeCheck) (AST.Module f' f) = InhTC
type instance Atts (Synthesized TypeCheck) (AST.Module f' f) = SynTCMod
type instance Atts (Inherited TypeCheck) (AST.Declaration f' f) = (InhTC, Map AST.Ident AST.Ident)
type instance Atts (Synthesized TypeCheck) (AST.Declaration f' f) = SynTCMod
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
   attribution TypeCheck (_, Modules self) (inherited, Modules ms) =
     (Synthesized SynTC{errors= foldMap (moduleErrors . syn) ms},
      Modules (Inherited InhTC{env= env (inh inherited) <> foldMap (moduleEnv . syn) ms} <$ self))

instance Attribution TypeCheck AST.Module (Int, AST.Module (Semantics TypeCheck) (Semantics TypeCheck)) where
   attribution TypeCheck (pos, AST.Module ident1 imports decls body ident2) (inherited, AST.Module _ _ decls' body' _) =
      (Synthesized SynTCMod{moduleErrors= foldMap (moduleErrors . syn) decls' <> foldMap (errors . syn) body',
                            moduleEnv= exportedEnv,
                            pointerTargets= pointers},
       AST.Module ident1 imports [Inherited (localEnv, pointers)] (Inherited localEnv <$ body) ident2)
      where exportedEnv = exportNominal <$> Map.mapKeysMonotonic export newEnv
            newEnv = Map.unionsWith mergeTypeBoundProcedures (moduleEnv . syn <$> decls')
            localEnv = InhTC (newEnv `Map.union` env (inh inherited))
            export (AST.NonQualIdent name) = AST.QualIdent ident1 name
            export q = q
            exportNominal (NominalType (AST.NonQualIdent name) (Just t)) =
              NominalType (AST.QualIdent ident1 name) (Just $ exportNominal' t)
            exportNominal t = exportNominal' t
            exportNominal' (RecordType ancestry fields) = RecordType (export <$> ancestry) (exportNominal' <$> fields)
            exportNominal' (ProcedureType False parameters result) =
              ProcedureType False ((exportNominal' <$>) <$> parameters) (exportNominal' <$> result)
            exportNominal' (PointerType target) = PointerType (exportNominal' target)
            exportNominal' (ArrayType dimensions itemType) = ArrayType dimensions (exportNominal' itemType)
            exportNominal' (NominalType q@(AST.NonQualIdent name) (Just t)) =
              fromMaybe (NominalType (AST.QualIdent ident1 name) $ Just $ exportNominal' t) (Map.lookup q exportedEnv)
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
               (inherited, AST.ConstantDeclaration _ expression) =
      (Synthesized SynTCMod{moduleErrors= expressionErrors (syn expression),
                            moduleEnv= Map.singleton (AST.NonQualIdent name) (inferredType $ syn expression),
                            pointerTargets= mempty},
       AST.ConstantDeclaration namedef (Inherited $ fst $ inh inherited))
   attribution TypeCheck (pos, AST.TypeDeclaration namedef@(AST.IdentDef name _) _)
               (inherited, AST.TypeDeclaration _ definition) =
      (Synthesized SynTCMod{moduleErrors= typeErrors (syn definition),
                            moduleEnv= Map.singleton qname (nominal $ definedType $ syn definition),
                            pointerTargets= foldMap (Map.singleton name) (pointerTarget $ syn definition)},
       AST.TypeDeclaration namedef (Inherited $ fst $ inh inherited))
      where nominal t@NominalType{} = t
            nominal (PointerType t@RecordType{})
              | AST.NonQualIdent n <- qname =
                  NominalType qname (Just $ PointerType $ NominalType (AST.NonQualIdent $ n<>"^") (Just t))
            nominal t = NominalType qname (Just t)
            qname = AST.NonQualIdent name
   attribution TypeCheck (pos, AST.VariableDeclaration names _declaredType)
               (inherited, AST.VariableDeclaration _names declaredType) =
      (Synthesized SynTCMod{moduleErrors= typeErrors (syn declaredType) 
                                          <> case definedType (syn declaredType)
                                             of ArrayType [] _ -> [(pos, OpenArrayVariable)]
                                                _ -> [],
                            moduleEnv= foldMap (\name-> Map.singleton (AST.NonQualIdent $ defName name)
                                                        (definedType $ syn declaredType))
                                       names,
                            pointerTargets= mempty},
       AST.VariableDeclaration names (Inherited $ fst $ inh inherited))
      where defName (AST.IdentDef name _) = name
   attribution TypeCheck (pos, AST.ProcedureDeclaration (AST.ProcedureHeading receiver indirect
                                                         namedef@(AST.IdentDef name _) signature) 
                               _body name')
               (inherited,
                AST.ProcedureDeclaration (AST.ProcedureHeading _receiver _indirect _ signature') 
                 body@(AST.ProcedureBody declarations statements) _name') =
      (Synthesized SynTCMod{moduleErrors= foldMap (signatureErrors . syn) signature'
                                          <> foldMap (moduleErrors . syn) declarations
                                          <> foldMap (errors . syn) statements,
                            moduleEnv= case receiver
                                       of Just (_, _, typeName)
                                             | Just targetName <- Map.lookup typeName (snd $ inh inherited) ->
                                                Map.singleton (AST.NonQualIdent targetName) methodType
                                             | otherwise -> Map.singleton (AST.NonQualIdent typeName) methodType
                                                
                                          Nothing -> Map.singleton (AST.NonQualIdent name) procedureType,
                            pointerTargets= mempty},
       AST.ProcedureDeclaration
          (AST.ProcedureHeading receiver indirect namedef (Inherited (fst $ inh inherited) <$ signature))
          (AST.ProcedureBody [Inherited (localInherited, mempty)] (Just $ Inherited localInherited))
          name')
     where receiverEnv (_, formalName, typeName) =
             foldMap (Map.singleton (AST.NonQualIdent formalName) . ReceiverType)
                     (Map.lookup (AST.NonQualIdent typeName) $ env $ fst $ inh inherited)
           methodType = NominalType (AST.NonQualIdent "") (Just $ RecordType [] $ Map.singleton name procedureType)
           procedureType = maybe (ProcedureType False [] Nothing) (signatureType . syn) signature'
           receiverError (_, formalName, typeName) =
             case Map.lookup (AST.NonQualIdent typeName) (env $ fst $ inh inherited)
             of Nothing -> [UnknownName $ AST.NonQualIdent typeName]
                Just RecordType{} -> []
                Just (PointerType RecordType{}) -> []
                Just (NominalType _ (Just RecordType{})) -> []
                Just (NominalType _ (Just (PointerType RecordType{}))) -> []
                Just t -> [NonRecordType t]
           localInherited = InhTC (foldMap (moduleEnv . syn) declarations <> env bodyInherited)
           bodyInherited = InhTC (foldMap receiverEnv receiver
                                  `Map.union` foldMap (signatureEnv . syn) signature'
                                  `Map.union` env (fst $ inh inherited))
   attribution TypeCheck (pos, AST.ForwardDeclaration namedef@(AST.IdentDef name _) signature)
               (inherited, AST.ForwardDeclaration _namedef signature') =
      (Synthesized SynTCMod{moduleErrors= foldMap (signatureErrors . syn) signature',
                            moduleEnv= foldMap (Map.singleton (AST.NonQualIdent name) . signatureType . syn) signature',
                            pointerTargets= mempty},
       AST.ForwardDeclaration namedef (Inherited (fst $ inh inherited) <$ signature))

instance Attribution TypeCheck AST.FormalParameters (Int, AST.FormalParameters (Semantics TypeCheck) (Semantics TypeCheck)) where
   attribution TypeCheck (pos, AST.FormalParameters sections returnType)
               (inherited, AST.FormalParameters sections' _returnType) =
      (Synthesized SynTCSig{signatureErrors= foldMap (sectionErrors . syn) sections' <> foldMap typeRefErrors returnType,
                            signatureType= ProcedureType False (foldMap (sectionParameters . syn) sections')
                                           $ returnType >>= (`Map.lookup` env (inh inherited)),
                            signatureEnv= foldMap (sectionEnv . syn) sections'},
       AST.FormalParameters (pure $ Inherited $ inh inherited) returnType)
      where typeRefErrors q
               | Map.member q (env $ inh inherited) = []
               | otherwise = [(pos, UnknownName q)]

instance Attribution TypeCheck AST.FPSection (Int, AST.FPSection (Semantics TypeCheck) (Semantics TypeCheck)) where
   attribution TypeCheck (pos, AST.FPSection var names _typeDef) (inherited, AST.FPSection _var _names typeDef) =
      (Synthesized SynTCSec{sectionErrors= typeErrors (syn typeDef),
                            sectionParameters= (var, definedType (syn typeDef)) <$ toList names,
                            sectionEnv= Map.fromList (toList
                                                      $ flip (,) (definedType $ syn typeDef) . AST.NonQualIdent 
                                                      <$> names)},
       AST.FPSection var names (Inherited $ inh inherited))

instance Attribution TypeCheck AST.Type (Int, AST.Type (Semantics TypeCheck) (Semantics TypeCheck)) where
   attribution TypeCheck (pos, AST.TypeReference q) (inherited, _) = 
      (Synthesized SynTCType{typeErrors= if Map.member q (env $ inh inherited) then [] else [(pos, UnknownName q)],
                             typeName= case q 
                                       of AST.NonQualIdent name -> Just name
                                          _ -> Nothing,
                             pointerTarget= Nothing,
                             definedType= fromMaybe UnknownType (Map.lookup q $ env $ inh inherited)},
       AST.TypeReference q)
   attribution TypeCheck (pos, AST.ArrayType dimensions _itemType) (inherited, AST.ArrayType dimensions' itemType) = 
      (Synthesized SynTCType{typeErrors= foldMap (expressionErrors . syn) dimensions' <> typeErrors (syn itemType)
                                         <> foldMap (expectInteger . syn) dimensions',
                             typeName= Nothing,
                             pointerTarget= Nothing,
                             definedType= ArrayType (integerValue . syn <$> dimensions') (definedType $ syn itemType)},
       AST.ArrayType [Inherited (inh inherited)] (Inherited $ inh inherited))
     where expectInteger SynTCExp{inferredType= IntegerType{}} = []
           expectInteger SynTCExp{inferredType= t} = [(pos, NonIntegerType t)]
           integerValue SynTCExp{inferredType= IntegerType n} = n
           integerValue _ = 0
   attribution TypeCheck (pos, AST.RecordType base fields) (inherited, AST.RecordType _base fields') =
      (Synthesized SynTCType{typeErrors= fst baseRecord <> foldMap (fieldErrors . syn) fields',
                             typeName= Nothing,
                             pointerTarget= Nothing,
                             definedType= RecordType (maybe [] (maybe id (:) base . ancestry) $ snd baseRecord)
                                             (maybe Map.empty recordFields (snd baseRecord)
                                              <> foldMap (fieldEnv . syn) fields')},
       AST.RecordType base (pure $ Inherited $ inh inherited))
     where baseRecord = case flip Map.lookup (env $ inh inherited) <$> base
                        of Just (Just t@RecordType{}) -> ([], Just t)
                           Just (Just (NominalType _ (Just t@RecordType{}))) -> ([], Just t)
                           Just (Just t) -> ([(pos, NonRecordType t)], Nothing)
                           Just Nothing -> (foldMap ((:[]) . (,) pos . UnknownName) base, Nothing)
                           Nothing -> ([], Nothing)
   attribution TypeCheck _self (inherited, AST.PointerType targetType') =
      (Synthesized SynTCType{typeErrors= typeErrors (syn targetType'),
                             typeName= Nothing,
                             pointerTarget= typeName (syn targetType'),
                             definedType= PointerType (definedType $ syn targetType')},
       AST.PointerType (Inherited $ inh inherited))
   attribution TypeCheck (pos, AST.ProcedureType signature) (inherited, AST.ProcedureType signature') = 
      (Synthesized SynTCType{typeErrors= foldMap (signatureErrors . syn) signature',
                             typeName= Nothing,
                             pointerTarget= Nothing,
                             definedType= maybe (ProcedureType False [] Nothing) (signatureType . syn) signature'},
       AST.ProcedureType (Inherited (inh inherited) <$ signature))

instance Attribution TypeCheck AST.FieldList (Int, AST.FieldList (Semantics TypeCheck) (Semantics TypeCheck)) where
   attribution TypeCheck (pos, AST.FieldList names _declaredType) (inherited, AST.FieldList _names declaredType) =
      (Synthesized SynTCFields{fieldErrors= typeErrors (syn declaredType),
                               fieldEnv= foldMap (\name-> Map.singleton (defName name) (definedType $ syn declaredType)) 
                                         names},
       AST.FieldList names (Inherited $ inh inherited))
      where defName (AST.IdentDef name _) = name
   attribution TypeCheck self (inherited, AST.EmptyFieldList) =
     (Synthesized SynTCFields{fieldErrors= [], fieldEnv= mempty},
      AST.EmptyFieldList)

instance Attribution TypeCheck (Deep.Product AST.Expression AST.StatementSequence) (Int, (Deep.Product AST.Expression AST.StatementSequence) (Semantics TypeCheck) (Semantics TypeCheck)) where
   attribution TypeCheck (pos, _) (inherited, Deep.Pair condition statements) =
      (Synthesized SynTC{errors= booleanExpressionErrors pos (syn condition) <> errors (syn statements)},
       Deep.Pair (Inherited $ inh inherited) (Inherited $ inh inherited))

instance Attribution TypeCheck AST.StatementSequence (Int, AST.StatementSequence (Semantics TypeCheck) (Semantics TypeCheck)) where
   attribution TypeCheck (pos, AST.StatementSequence statements) (inherited, AST.StatementSequence statements') =
      (Synthesized SynTC{errors= foldMap (errors . syn) statements'},
       AST.StatementSequence (pure $ Inherited $ inh inherited))

instance Attribution TypeCheck AST.Statement (Int, AST.Statement (Semantics TypeCheck) (Semantics TypeCheck)) where
   attribution TypeCheck _ (inherited, AST.EmptyStatement) = (Synthesized SynTC{errors= []}, AST.EmptyStatement)
   attribution TypeCheck (pos, _) (inherited, AST.Assignment var value) = {-# SCC "Assignment" #-}
      (Synthesized SynTC{errors= assignmentCompatible pos (designatorType $ syn var) (inferredType $ syn value)},
       AST.Assignment (Inherited $ inh inherited) (Inherited $ inh inherited))
   attribution TypeCheck (pos, AST.ProcedureCall _proc parameters) (inherited, AST.ProcedureCall procedure' parameters') =
      (Synthesized SynTC{errors= case syn procedure'
                                 of SynTCDes{designatorErrors= [],
                                             designatorType= t} -> procedureErrors t
                                    SynTCDes{designatorErrors= errs} -> errs
                                      <> foldMap (foldMap (expressionErrors . syn)) parameters'},
       AST.ProcedureCall (Inherited $ inh inherited) (Just [Inherited $ inh inherited]))
     where procedureErrors (ProcedureType _ formalTypes Nothing)
             | length formalTypes /= maybe 0 length parameters,
               not (length formalTypes == 2 && (length <$> parameters) == Just 1
                    && designatorSelf (syn procedure') == AST.Variable (AST.NonQualIdent "ASSERT")
                    || length formalTypes == 1 && (length <$> parameters) == Just 2
                    && designatorSelf (syn procedure') == AST.Variable (AST.NonQualIdent "NEW")
                    && all (all (isIntegerType . inferredType . syn) . tail) parameters') =
                 [(pos, ArgumentCountMismatch (length formalTypes) $ maybe 0 length parameters)]
             | otherwise = concat (zipWith (parameterCompatible pos) formalTypes
                                   $ maybe [] (inferredType . syn <$>) parameters')
           procedureErrors (NominalType _ (Just t)) = procedureErrors t
           procedureErrors t = [(pos, NonProcedureType t)]
   attribution TypeCheck self (inherited, AST.If branches fallback) =
      (Synthesized SynTC{errors= foldMap (errors . syn) branches <> foldMap (errors . syn) fallback},
       AST.If (pure $ Inherited $ inh inherited) (Just $ Inherited $ inh inherited))
   attribution TypeCheck self (inherited, AST.CaseStatement value branches fallback) =
      (Synthesized SynTC{errors= expressionErrors (syn value) <> foldMap (errors . syn) branches
                                 <> foldMap (errors . syn) fallback},
       AST.CaseStatement (Inherited $ inh inherited) (pure $ Inherited (inh inherited, inferredType $ syn value))
                         (Just $ Inherited $ inh inherited))
   attribution TypeCheck (pos, _) (inherited, AST.While condition body) =
      (Synthesized SynTC{errors= booleanExpressionErrors pos (syn condition) <> errors (syn body)},
       AST.While (Inherited $ inh inherited) (Inherited $ inh inherited))
   attribution TypeCheck (pos, _) (inherited, AST.Repeat body condition) =
      (Synthesized SynTC{errors= booleanExpressionErrors pos (syn condition) <> errors (syn body)},
       AST.Repeat (Inherited $ inh inherited) (Inherited $ inh inherited))
   attribution TypeCheck (pos, AST.For counter _start _end _step _body) (inherited, AST.For _counter start end step body) =
      (Synthesized SynTC{errors= integerExpressionErrors pos (syn start) <> integerExpressionErrors pos (syn end)
                                 <> foldMap (integerExpressionErrors pos . syn) step <> errors (syn body)},
       AST.For counter (Inherited $ inh inherited) (Inherited $ inh inherited) (Just $ Inherited $ inh inherited)
                       (Inherited $ InhTC $
                        Map.insert (AST.NonQualIdent counter) (NominalType (AST.NonQualIdent "INTEGER") Nothing)
                        $ env $ inh inherited))
   attribution TypeCheck self (inherited, AST.Loop body) = (Synthesized SynTC{errors= errors (syn body)},
                                                            AST.Loop (Inherited $ inh inherited))
   attribution TypeCheck self (inherited, AST.With branches fallback) =
      (Synthesized SynTC{errors= foldMap (errors . syn) branches <> foldMap (errors . syn) fallback},
       AST.With (pure $ Inherited $ inh inherited) (Just $ Inherited $ inh inherited))
   attribution TypeCheck self (inherited, AST.Exit) = (Synthesized SynTC{errors= []}, AST.Exit)
   attribution TypeCheck self (inherited, AST.Return value) =
      (Synthesized SynTC{errors= foldMap (expressionErrors . syn) value}, 
       AST.Return (Just $ Inherited $ inh inherited))

instance Attribution TypeCheck AST.WithAlternative (Int, AST.WithAlternative (Semantics TypeCheck) (Semantics TypeCheck)) where
   attribution TypeCheck (pos, AST.WithAlternative var subtype _body)
                         (inherited, AST.WithAlternative _var _subtype body) =
      (Synthesized SynTC{errors= case (Map.lookup var (env $ inh inherited),
                                       Map.lookup subtype (env $ inh inherited))
                                 of (Just supertype, Just subtypeDef) -> assignmentCompatible pos supertype subtypeDef
                                    (Nothing, _) -> [(pos, UnknownName var)]
                                    (_, Nothing) -> [(pos, UnknownName subtype)]
                                 <> errors (syn body)},
       AST.WithAlternative var subtype (Inherited $ InhTC $
                                        maybe id (Map.insert var) (Map.lookup subtype $ env $ inh inherited) 
                                        $ env $ inh inherited))

instance Attribution TypeCheck AST.Case (Int, AST.Case (Semantics TypeCheck) (Semantics TypeCheck)) where
   attribution TypeCheck self (inherited, AST.Case labels body) =
      (Synthesized SynTC{errors= foldMap (errors . syn) labels <> errors (syn body)},
       AST.Case (pure $ Inherited $ inh inherited) (Inherited $ fst $ inh inherited))
   attribution TypeCheck self (inherited, AST.EmptyCase) = (Synthesized SynTC{errors= []}, AST.EmptyCase)

instance Attribution TypeCheck AST.CaseLabels (Int, AST.CaseLabels (Semantics TypeCheck) (Semantics TypeCheck)) where
   attribution TypeCheck (pos, _) (inherited, AST.SingleLabel value) =
      (Synthesized SynTC{errors= assignmentCompatible pos (snd $ inh inherited) (inferredType $ syn value)},
       AST.SingleLabel (Inherited $ fst $ inh inherited))
   attribution TypeCheck (pos, _) (inherited, AST.LabelRange start end) =
      (Synthesized SynTC{errors= assignmentCompatible pos (snd $ inh inherited) (inferredType $ syn start)
                                 <> assignmentCompatible pos (snd $ inh inherited) (inferredType $ syn end)},
       AST.LabelRange (Inherited $ fst $ inh inherited) (Inherited $ fst $ inh inherited))

instance Attribution TypeCheck AST.Expression (Int, AST.Expression (Semantics TypeCheck) (Semantics TypeCheck)) where
   attribution TypeCheck (pos, AST.Relation op _ _) (inherited, AST.Relation _op left right) =
      (Synthesized SynTCExp{expressionErrors= case expressionErrors (syn left) <> expressionErrors (syn right)
                                              of [] | t1 == t2 -> []
                                                    | AST.Is <- op -> assignmentCompatible pos t1 t2
                                                    | AST.In <- op -> membershipCompatible (ultimate t1) (ultimate t2)
                                                    | equality op, [] <- assignmentCompatible pos t1 t2 -> []
                                                    | equality op, [] <- assignmentCompatible pos t2 t1 -> []
                                                    | op /= AST.Is -> comparable (ultimate t1) (ultimate t2)
                                                    | otherwise -> [(pos, TypeMismatch t1 t2)]
                                                 errs -> errs,
                            inferredType= NominalType (AST.NonQualIdent "BOOLEAN") Nothing},
       AST.Relation op (Inherited $ inh inherited) (Inherited $ inh inherited))
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
            comparable t1 t2 = [(pos, IncomparableTypes t1 t2)]
            membershipCompatible IntegerType{} (NominalType (AST.NonQualIdent "SET") Nothing) = []
            membershipCompatible (NominalType (AST.NonQualIdent t) Nothing)
                                 (NominalType (AST.NonQualIdent "SET") Nothing) | isNumerical t = []
   attribution TypeCheck (pos, _) (inherited, AST.Positive expr) =
      (Synthesized SynTCExp{expressionErrors= unaryNumericOperatorErrors pos (syn expr),
                            inferredType= inferredType (syn expr)},
       AST.Positive (Inherited $ inh inherited))
   attribution TypeCheck (pos, _) (inherited, AST.Negative expr) =
      (Synthesized SynTCExp{expressionErrors= unaryNumericOperatorErrors pos (syn expr),
                            inferredType= unaryNumericOperatorType negate (syn expr)},
       AST.Negative (Inherited $ inh inherited))
   attribution TypeCheck (pos, _) (inherited, AST.Add left right) =
      (Synthesized SynTCExp{expressionErrors= binarySetOrNumericOperatorErrors pos (syn left) (syn right),
                            inferredType= binaryNumericOperatorType div (syn left) (syn right)},
       AST.Add (Inherited $ inh inherited) (Inherited $ inh inherited))
   attribution TypeCheck (pos, _) (inherited, AST.Subtract left right) =
      (Synthesized SynTCExp{expressionErrors= binarySetOrNumericOperatorErrors pos (syn left) (syn right),
                            inferredType= binaryNumericOperatorType div (syn left) (syn right)},
       AST.Subtract (Inherited $ inh inherited) (Inherited $ inh inherited))
   attribution TypeCheck (pos, _) (inherited, AST.Or left right) =
      (Synthesized SynTCExp{expressionErrors= binaryBooleanOperatorErrors pos (syn left) (syn right),
                            inferredType= NominalType (AST.NonQualIdent "BOOLEAN") Nothing},
       AST.Or (Inherited $ inh inherited) (Inherited $ inh inherited))
   attribution TypeCheck (pos, _) (inherited, AST.Multiply left right) =
      (Synthesized SynTCExp{expressionErrors= binarySetOrNumericOperatorErrors pos (syn left) (syn right),
                            inferredType= binaryNumericOperatorType div (syn left) (syn right)},
       AST.Multiply (Inherited $ inh inherited) (Inherited $ inh inherited))
   attribution TypeCheck (pos, _) (inherited, AST.Divide left right) =
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
                                    | t1 == t2 -> [(pos, UnrealType t1)]
                                    | otherwise -> [(pos, TypeMismatch t1 t2)],
                            inferredType= NominalType (AST.NonQualIdent "REAL") Nothing},
       AST.Divide (Inherited $ inh inherited) (Inherited $ inh inherited))
   attribution TypeCheck (pos, _) (inherited, AST.IntegerDivide left right) =
      (Synthesized SynTCExp{expressionErrors= binaryIntegerOperatorErrors pos (syn left) (syn right),
                            inferredType= binaryNumericOperatorType div (syn left) (syn right)},
       AST.IntegerDivide (Inherited $ inh inherited) (Inherited $ inh inherited))
   attribution TypeCheck (pos, _) (inherited, AST.Modulo left right) =
      (Synthesized SynTCExp{expressionErrors= binaryIntegerOperatorErrors pos (syn left) (syn right),
                            inferredType= binaryNumericOperatorType mod (syn left) (syn right)},
        AST.Modulo (Inherited $ inh inherited) (Inherited $ inh inherited))
   attribution TypeCheck (pos, _) (inherited, AST.And left right) =
      (Synthesized SynTCExp{expressionErrors= binaryBooleanOperatorErrors pos (syn left) (syn right),
                            inferredType= NominalType (AST.NonQualIdent "BOOLEAN") Nothing},
       AST.And (Inherited $ inh inherited) (Inherited $ inh inherited))
   attribution TypeCheck (pos, AST.Integer x) (inherited, _) =
      (Synthesized SynTCExp{expressionErrors= mempty,
                            inferredType= IntegerType (read $ Text.unpack x)},
       AST.Integer x)
   attribution TypeCheck self (inherited, AST.Real x) =
      (Synthesized SynTCExp{expressionErrors= mempty,
                            inferredType= NominalType (AST.NonQualIdent "REAL") Nothing},
       AST.Real x)
   attribution TypeCheck self (inherited, AST.CharConstant x) =
      (Synthesized SynTCExp{expressionErrors= mempty,
                            inferredType= NominalType (AST.NonQualIdent "CHAR") Nothing},
       AST.CharConstant x)
   attribution TypeCheck self (inherited, AST.CharCode x) =
      (Synthesized SynTCExp{expressionErrors= mempty,
                            inferredType= NominalType (AST.NonQualIdent "CHAR") Nothing},
       AST.CharCode x)
   attribution TypeCheck (pos, AST.String x) (inherited, _) =
      (Synthesized SynTCExp{expressionErrors= mempty,
                            inferredType= StringType (Text.length x)},
       AST.String x)
   attribution TypeCheck self (inherited, AST.Nil) =
      (Synthesized SynTCExp{expressionErrors= mempty,
                            inferredType= NilType},
       AST.Nil)
   attribution TypeCheck self (inherited, AST.Set elements) =
      (Synthesized SynTCExp{expressionErrors= mempty,
                            inferredType= NominalType (AST.NonQualIdent "SET") Nothing},
       AST.Set [Inherited $ inh inherited])
   attribution TypeCheck self (inherited, AST.Read designator) =
      (Synthesized SynTCExp{expressionErrors= designatorErrors (syn designator),
                            inferredType= designatorType (syn designator)},
       AST.Read (Inherited $ inh inherited))
   attribution TypeCheck (pos, AST.FunctionCall _designator parameters)
               (inherited, AST.FunctionCall designator parameters') =
      (Synthesized SynTCExp{expressionErrors= case {-# SCC "FunctionCall" #-} syn designator
                                              of SynTCDes{designatorErrors= [],
                                                          designatorType= ProcedureType _ formalTypes Just{}}
                                                   | length formalTypes /= length parameters ->
                                                       [(pos,
                                                         ArgumentCountMismatch (length formalTypes)
                                                                               (length parameters))]
                                                   | otherwise -> concat (zipWith (parameterCompatible pos) formalTypes
                                                                          $ inferredType . syn <$> parameters')
                                                 SynTCDes{designatorErrors= [],
                                                          designatorType= t} -> [(pos, NonFunctionType t)]
                                                 SynTCDes{designatorErrors= errs} -> errs
                                              <> foldMap (expressionErrors . syn) parameters',
                            inferredType= case syn designator
                                          of SynTCDes{designatorSelf= d,
                                                      designatorType= t}
                                               | ProcedureType _ _ (Just returnType) <- ultimate t ->
                                                   case returnType
                                                   of IntegerType{} ->
                                                        IntegerType (callValue d $ inferredType . syn <$> parameters')
                                                      _ -> returnType
                                             _ -> UnknownType},
       AST.FunctionCall (Inherited $ inh inherited) [Inherited $ inh inherited])
     where callValue (AST.Variable (AST.NonQualIdent "MAX"))
                     [NominalType (AST.NonQualIdent t) Nothing] =
             case t
             of "SET" -> 63
                "SHORTINT" -> 2^15-1
                "INTEGER" -> 2^31-1
                "LONGLINT" -> 2^63-1
           callValue (AST.Variable (AST.NonQualIdent "MIN"))
                     [NominalType (AST.NonQualIdent t) Nothing] =
             case t
             of "SET" -> 0
                "SHORTINT" -> -2^15
                "INTEGER" -> -2^31
                "LONGLINT" -> -2^63
   attribution TypeCheck (pos, _) (inherited, AST.Not expr) =
      (Synthesized SynTCExp{expressionErrors= booleanExpressionErrors pos (syn expr),
                            inferredType= NominalType (AST.NonQualIdent "BOOLEAN") Nothing},
       AST.Not (Inherited $ inh inherited))

instance Attribution TypeCheck AST.Element (Int, AST.Element (Semantics TypeCheck) (Semantics TypeCheck)) where
   attribution TypeCheck (pos, _) (inherited, AST.Element expr) =
      (Synthesized SynTCExp{expressionErrors= integerExpressionErrors pos (syn expr),
                            inferredType= NominalType (AST.NonQualIdent "SET") Nothing},
       AST.Element (Inherited $ inh inherited))
   attribution TypeCheck (pos, _) (inherited, AST.Range low high) =
      (Synthesized SynTCExp{expressionErrors= integerExpressionErrors pos (syn low)
                                              <> integerExpressionErrors pos (syn high),
                            inferredType= NominalType (AST.NonQualIdent "SET") Nothing},
       AST.Range (Inherited $ inh inherited) (Inherited $ inh inherited))

instance Attribution TypeCheck AST.Designator (Int, AST.Designator (Semantics TypeCheck) (Semantics TypeCheck)) where
   attribution TypeCheck (pos, AST.Variable q) (inherited, _) =
      (Synthesized SynTCDes{designatorErrors= case designatorType
                                              of Nothing -> [(pos, UnknownName q)]
                                                 Just{} -> [],
                            designatorSelf= AST.Variable q,
                            designatorType= fromMaybe UnknownType designatorType},
       AST.Variable q)
      where designatorType = Map.lookup q (env $ inh inherited)
   attribution TypeCheck (pos, AST.Field _record fieldName) (inherited, AST.Field record _fieldName) =
      (Synthesized SynTCDes{designatorErrors= case syn record
                                              of SynTCDes{designatorErrors= [],
                                                          designatorType= t} ->
                                                   maybe [(pos, NonRecordType t)]
                                                         (maybe [(pos, UnknownField fieldName t)] $ const [])
                                                         (access True t)
                                                 SynTCDes{designatorErrors= errors} -> errors,
                            designatorSelf= AST.Field (Identity $ designatorSelf $ syn record) fieldName,
                            designatorType= fromMaybe UnknownType (fromMaybe Nothing $ access True
                                                                   $ designatorType $ syn record)},
       AST.Field (Inherited $ inh inherited) fieldName)
     where access _ (RecordType _ fields) = Just (Map.lookup fieldName fields)
           access True (PointerType t) = access False t
           access allowPtr (NominalType _ (Just t)) = access allowPtr t
           access allowPtr (ReceiverType t) = (receive <$>) <$> access allowPtr t
           access _ _ = Nothing
           receive (ProcedureType _ params result) = ProcedureType True params result
           receive t = t
   attribution TypeCheck (pos, AST.Index _array indexes) (inherited, AST.Index array _indexes) =
      (Synthesized SynTCDes{designatorErrors= case syn array
                                              of SynTCDes{designatorErrors= [],
                                                          designatorType= t} ->
                                                   either id (const []) (access True t)
                                                 SynTCDes{designatorErrors= errors} -> errors,
                            designatorType= either (const UnknownType) id (access True $ designatorType $ syn array)},
       AST.Index (Inherited $ inh inherited) (pure $ Inherited $ inh inherited))
      where access _ (ArrayType dimensions t)
              | length dimensions == length indexes = Right t
              | length dimensions == 0 && length indexes == 1 = Right t
              | otherwise = Left [(pos, ExtraDimensionalIndex t)]
            access allowPtr (NominalType _ (Just t)) = access allowPtr t
            access allowPtr (ReceiverType t) = access allowPtr t
            access True (PointerType t) = access False t
            access _ t = Left [(pos, NonArrayType t)]
   attribution TypeCheck (pos, AST.TypeGuard _designator q) (inherited, AST.TypeGuard designator _q) =
      (Synthesized SynTCDes{designatorErrors= case (syn designator, targetType)
                                              of (SynTCDes{designatorErrors= [],
                                                           designatorType= t}, 
                                                  Just t') -> assignmentCompatible pos t t'
                                                 (SynTCDes{designatorErrors= errors}, 
                                                  Nothing) -> (pos, UnknownName q) : errors
                                                 (SynTCDes{designatorErrors= errors}, _) -> errors,
                            designatorType= fromMaybe UnknownType targetType},
       AST.TypeGuard (Inherited $ inh inherited) q)
      where targetType = Map.lookup q (env $ inh inherited)
   attribution TypeCheck (pos, _) (inherited, AST.Dereference pointer) =
      (Synthesized SynTCDes{designatorErrors= case syn pointer
                                              of SynTCDes{designatorErrors= [],
                                                          designatorType= PointerType{}} -> []
                                                 SynTCDes{designatorErrors= [],
                                                          designatorType= NominalType _ (Just PointerType{})} -> []
                                                 SynTCDes{designatorErrors= [],
                                                          designatorType= ProcedureType True _ _} -> []
                                                 SynTCDes{designatorErrors= [],
                                                          designatorType= t} -> [(pos, NonPointerType t)]
                                                 SynTCDes{designatorErrors= errors} -> errors,
                            designatorType= case designatorType (syn pointer)
                                            of NominalType _ (Just (PointerType t)) -> t
                                               ProcedureType True params result -> ProcedureType False params result
                                               PointerType t -> t
                                               _ -> UnknownType},
       AST.Dereference (Inherited $ inh inherited))

unaryNumericOperatorErrors :: Int -> SynTCExp -> [Error]
unaryNumericOperatorErrors _ SynTCExp{expressionErrors= [], inferredType= IntegerType{}} = []
unaryNumericOperatorErrors _ SynTCExp{expressionErrors= [],
                                      inferredType= NominalType (AST.NonQualIdent name) Nothing}
  | isNumerical name = []
unaryNumericOperatorErrors pos SynTCExp{expressionErrors= [], inferredType= t} = [(pos, NonNumericType t)]
unaryNumericOperatorErrors _ SynTCExp{expressionErrors= errs} = errs

unaryNumericOperatorType :: (Int -> Int) -> SynTCExp -> Type
unaryNumericOperatorType f SynTCExp{inferredType= IntegerType x} = IntegerType (f x)
unaryNumericOperatorType _ SynTCExp{inferredType= t} = t

binarySetOrNumericOperatorErrors :: Int -> SynTCExp -> SynTCExp -> [Error]
binarySetOrNumericOperatorErrors _
  SynTCExp{expressionErrors= [], inferredType= NominalType (AST.NonQualIdent name1) Nothing}
  SynTCExp{expressionErrors= [], inferredType= NominalType (AST.NonQualIdent name2) Nothing}
  | isNumerical name1, isNumerical name2 = []
  | name1 == "SET", name2 == "SET" = []
binarySetOrNumericOperatorErrors _
  SynTCExp{expressionErrors= [], inferredType= IntegerType{}}
  SynTCExp{expressionErrors= [], inferredType= NominalType (AST.NonQualIdent name) Nothing}
  | isNumerical name = []
binarySetOrNumericOperatorErrors _
  SynTCExp{expressionErrors= [], inferredType= NominalType (AST.NonQualIdent name) Nothing}
  SynTCExp{expressionErrors= [], inferredType= IntegerType{}}
  | isNumerical name = []
binarySetOrNumericOperatorErrors _
  SynTCExp{expressionErrors= [], inferredType= IntegerType{}}
  SynTCExp{expressionErrors= [], inferredType= IntegerType{}} = []
binarySetOrNumericOperatorErrors pos SynTCExp{expressionErrors= [], inferredType= t1}
                                SynTCExp{expressionErrors= [], inferredType= t2}
  | t1 == t2 = [(pos, NonNumericType t1)]
  | otherwise = [(pos, TypeMismatch t1 t2)]
binarySetOrNumericOperatorErrors _ SynTCExp{expressionErrors= errs1} SynTCExp{expressionErrors= errs2} = errs1 <> errs2

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

binaryIntegerOperatorErrors :: Int ->  SynTCExp -> SynTCExp -> [Error]
binaryIntegerOperatorErrors pos syn1 syn2 = integerExpressionErrors pos syn1 <> integerExpressionErrors pos syn2

integerExpressionErrors pos SynTCExp{expressionErrors= [], inferredType= t}
  | isIntegerType t = []
  | otherwise = [(pos, NonIntegerType t)]
integerExpressionErrors _ SynTCExp{expressionErrors= errs} = errs

isIntegerType IntegerType{} = True
isIntegerType (NominalType (AST.NonQualIdent "SHORTINT") Nothing) = True
isIntegerType (NominalType (AST.NonQualIdent "INTEGER") Nothing) = True
isIntegerType (NominalType (AST.NonQualIdent "LONGINT") Nothing) = True
isIntegerType t = False

booleanExpressionErrors _ SynTCExp{expressionErrors= [],
                                   inferredType= NominalType (AST.NonQualIdent "BOOLEAN") Nothing} = []
booleanExpressionErrors pos SynTCExp{expressionErrors= [], inferredType= t} = [(pos, NonBooleanType t)]
booleanExpressionErrors _ SynTCExp{expressionErrors= errs} = errs

binaryBooleanOperatorErrors :: Int -> SynTCExp -> SynTCExp -> [Error]
binaryBooleanOperatorErrors _pos
  SynTCExp{expressionErrors= [], inferredType= NominalType (AST.NonQualIdent "BOOLEAN") Nothing}
  SynTCExp{expressionErrors= [], inferredType= NominalType (AST.NonQualIdent "BOOLEAN") Nothing} = []
binaryBooleanOperatorErrors pos
  SynTCExp{expressionErrors= [], inferredType= t1}
  SynTCExp{expressionErrors= [], inferredType= t2}
  | t1 == t2 = [(pos, NonBooleanType t1)]
  | otherwise = [(pos, TypeMismatch t1 t2)]
binaryBooleanOperatorErrors _ SynTCExp{expressionErrors= errs1} SynTCExp{expressionErrors= errs2} = errs1 <> errs2

parameterCompatible :: Int -> (Bool, Type) -> Type -> [Error]
parameterCompatible _ (_, expected@(ArrayType [] _)) actual
  | arrayCompatible expected actual = []
parameterCompatible pos (True, expected) actual
  | expected == actual = []
  | otherwise = [(pos, UnequalTypes expected actual)]
parameterCompatible pos (False, expected) actual
  | NominalType (AST.NonQualIdent "ARRAY") Nothing <- expected, ArrayType{} <- actual = []
  | otherwise = assignmentCompatible pos expected actual

assignmentCompatible :: Int -> Type -> Type -> [Error]
assignmentCompatible pos expected actual
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
       assignmentCompatible pos expected t
   | expected == NominalType (AST.NonQualIdent "CHAR") Nothing, actual == StringType 1 = []
   | ReceiverType t <- actual = assignmentCompatible pos expected t
   | ReceiverType t <- expected = assignmentCompatible pos t actual
   | NilType <- actual, PointerType{} <- expected = []
   | NilType <- actual, ProcedureType{} <- expected = []
   | NilType <- actual, NominalType _ (Just t) <- expected = assignmentCompatible pos t actual
--   | ArrayType [] (NominalType (AST.NonQualIdent "CHAR") Nothing) <- expected, StringType{} <- actual = []
   | ArrayType [m] (NominalType (AST.NonQualIdent "CHAR") Nothing) <- expected, StringType n <- actual = 
      if m < n then [(pos, TooSmallArrayType expected)] else []
   | targetExtends actual expected = []
   | NominalType _ (Just t) <- expected, ProcedureType{} <- actual = assignmentCompatible pos t actual
   | otherwise = [(pos, IncompatibleTypes expected actual)]

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
   AST.Module ident1a imports1 decls1 body1 ident1b <*> ~(AST.Module ident2a imports2 decls2 body2 ident2b) =
      AST.Module ident1a imports1 (liftA2 Rank2.apply decls1 decls2) (liftA2 Rank2.apply body1 body2) ident1b

type Placed = ((,) Int)

checkModules :: Environment -> Map AST.Ident (AST.Module Placed Placed) -> [Error]
checkModules predef modules =
   errors (syn (TypeCheck Shallow.<$> (0, TypeCheck Deep.<$> Modules modules')
                `Rank2.apply`
                Inherited (InhTC predef)))
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
    ("MAX", ProcedureType False [(False, NominalType (AST.NonQualIdent "BASIC TYPE") Nothing)] $ Just $ IntegerType 0),
    ("MIN", ProcedureType False [(False, NominalType (AST.NonQualIdent "BASIC TYPE") Nothing)] $ Just $ IntegerType 0),
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
