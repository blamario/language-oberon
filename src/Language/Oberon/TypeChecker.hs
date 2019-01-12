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
import Transformation.AG (Attribution(..), Atts, Inherited(..), Synthesized(..), Semantics)

import qualified Language.Oberon.AST as AST

import Debug.Trace

data Type = NominalType AST.QualIdent (Maybe Type)
          | RecordType{ancestry :: [AST.QualIdent],
                       recordFields :: Map AST.Ident Type}
          | NilType
          | StringType Int
          | ArrayType [Int] Type
          | PointerType Type
          | ProcedureType [Type] (Maybe Type)
          | UnknownType

data Error = TypeMismatch Type Type
           | ArgumentCountMismatch [Type] Int
           | DuplicateBinding AST.Ident
           | ExtraDimensionalIndex Type
           | NonArrayType Type
           | NonBooleanType Type
           | NonFunctionType Type
           | NonIntegerType Type
           | NonNumericType Type
           | NonPointerType Type
           | NonProcedureType Type
           | NonRecordType Type
           | UnrealType Type
           | UnknownName AST.QualIdent
           | UnknownField AST.Ident Type
           deriving Show

instance Eq Type where
  NominalType q1 _ == NominalType q2 _ = q1 == q2
  ArrayType [] t1 == ArrayType [] t2 = t1 == t2
  ProcedureType p1 r1 == ProcedureType p2 r2 = r1 == r2 && p1 == p2
  _ == _ = False

instance Show Type where
  show (NominalType q t) = "Nominal " ++ show q -- ++ " " ++ show t
  show (RecordType ancestry fields) = "RecordType " ++ show ancestry ++ show (fst <$> Map.toList fields)
  show (ArrayType dimensions itemType) = "ArrayType " ++ show dimensions ++ " " ++ show itemType
  show (PointerType targetType) = "PointerType " ++ show targetType
  show (ProcedureType parameters result) = "ProcedureType " ++ show parameters ++ " " ++ show result
  show StringType{} = "StringType"
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
                         sectionParameters :: [Type]} deriving Show

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
type instance Atts (Inherited TypeCheck) (AST.Case f' f) = InhTC
type instance Atts (Synthesized TypeCheck) (AST.Case f' f) = SynTC
type instance Atts (Inherited TypeCheck) (AST.CaseLabels f' f) = InhTC
type instance Atts (Synthesized TypeCheck) (AST.CaseLabels f' f) = SynTC
type instance Atts (Inherited TypeCheck) (AST.WithAlternative f' f) = InhTC
type instance Atts (Synthesized TypeCheck) (AST.WithAlternative f' f) = SynTC

-- * Rules

instance Attribution TypeCheck Modules where
   attribution TypeCheck (Modules self) (inherited, Modules ms) =
     (Synthesized SynTC{errors= foldMap (moduleErrors . syn) ms},
      Modules (Inherited InhTC{env= env (inh inherited) <> foldMap (moduleEnv . syn) ms} <$ self))

instance Attribution TypeCheck AST.Module where
   attribution TypeCheck (AST.Module ident1 imports decls body ident2) (inherited, AST.Module _ _ decls' body' _) =
      (Synthesized SynTCMod{moduleErrors= foldMap (moduleErrors . syn) decls' <> foldMap (errors . syn) body',
                            moduleEnv= Map.mapKeysMonotonic export newEnv,
                            pointerTargets= pointers},
       AST.Module ident1 imports [Inherited (localEnv, pointers)] (Inherited localEnv <$ body) ident2)
      where newEnv = Map.unionsWith mergeTypeBoundProcedures (moduleEnv . syn <$> decls')
            localEnv = InhTC (newEnv `Map.union` env (inh inherited))
            export (AST.NonQualIdent name) = AST.QualIdent ident1 name
            pointers= foldMap (pointerTargets . syn) decls'
            mergeTypeBoundProcedures' t1 t2 = mergeTypeBoundProcedures t1 t2
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
            mergeTypeBoundProcedures t1 t2 = error (take 90 $ show (anonymize t1))

instance Attribution TypeCheck AST.Declaration where
   attribution TypeCheck (AST.ConstantDeclaration namedef@(AST.IdentDef name _) _)
               (inherited, AST.ConstantDeclaration _ expression) =
      (Synthesized SynTCMod{moduleErrors= expressionErrors (syn expression),
                            moduleEnv= Map.singleton (AST.NonQualIdent name) (inferredType $ syn expression),
                            pointerTargets= mempty},
       AST.ConstantDeclaration namedef (Inherited $ fst $ inh inherited))
   attribution TypeCheck (AST.TypeDeclaration namedef@(AST.IdentDef name _) _) (inherited,
                                                                                AST.TypeDeclaration _ definition) =
      (Synthesized SynTCMod{moduleErrors= typeErrors (syn definition),
                            moduleEnv= Map.singleton qname (nominal $ definedType $ syn definition),
                            pointerTargets= foldMap (Map.singleton name) (pointerTarget $ syn definition)},
       AST.TypeDeclaration namedef (Inherited $ fst $ inh inherited))
      where nominal t@NominalType{} = t
            nominal t = NominalType qname (Just t)
            qname = AST.NonQualIdent name
   attribution TypeCheck (AST.VariableDeclaration names _declaredType)
               (inherited, AST.VariableDeclaration _names declaredType) =
      (Synthesized SynTCMod{moduleErrors= typeErrors (syn declaredType),
                            moduleEnv= foldMap (\name-> Map.singleton (AST.NonQualIdent $ defName name)
                                                        (definedType $ syn declaredType))
                                       names,
                            pointerTargets= mempty},
       AST.VariableDeclaration names (Inherited $ fst $ inh inherited))
      where defName (AST.IdentDef name _) = name
   attribution TypeCheck (AST.ProcedureDeclaration (AST.ProcedureHeading receiver indirect
                                                       namedef@(AST.IdentDef name _) signature) 
                          _body name')
               (inherited,
                AST.ProcedureDeclaration (AST.ProcedureHeading _receiver _indirect _ signature') 
                 body@(AST.ProcedureBody declarations statements) _name') =
      (Synthesized SynTCMod{moduleErrors= foldMap (signatureErrors . syn) signature',
                            moduleEnv= case receiver
                                       of Just (_, _, typeName)
                                             | Just targetName <- Map.lookup typeName (snd $ inh inherited) ->
                                                Map.singleton (AST.NonQualIdent targetName) methodType
                                             | otherwise -> Map.singleton (AST.NonQualIdent typeName) methodType
                                                
                                          Nothing -> Map.singleton (AST.NonQualIdent name) procedureType,
                            pointerTargets= mempty},
       AST.ProcedureDeclaration
          (AST.ProcedureHeading receiver indirect namedef (Inherited (fst $ inh inherited) <$ signature))
          (AST.ProcedureBody [Inherited (localInherited, mempty)] (Inherited localInherited <$ statements))
          name')
     where receiverEnv (_, formalName, typeName) =
             foldMap (Map.singleton $ AST.NonQualIdent formalName) (Map.lookup (AST.NonQualIdent typeName) 
                                                                    $ env $ fst $ inh inherited)
           methodType = NominalType (AST.NonQualIdent "") (Just $ RecordType [] $ Map.singleton name procedureType)
           procedureType = maybe (ProcedureType [] Nothing) (signatureType . syn) signature'
           receiverError (_, formalName, typeName) =
             case Map.lookup (AST.NonQualIdent typeName) (env $ fst $ inh inherited)
             of Nothing -> [UnknownName $ AST.NonQualIdent typeName]
                Just RecordType{} -> []
                Just (PointerType RecordType{}) -> []
                Just (NominalType _ (Just RecordType{})) -> []
                Just (NominalType _ (Just (PointerType RecordType{}))) -> []
                Just t -> [NonRecordType t]
           localInherited = InhTC (foldMap receiverEnv receiver
                                   `Map.union` foldMap (signatureEnv . syn) signature'
                                   `Map.union` env (fst $ inh inherited))
   attribution TypeCheck (AST.ForwardDeclaration namedef@(AST.IdentDef name _) signature)
               (inherited, AST.ForwardDeclaration _namedef signature') =
      (Synthesized SynTCMod{moduleErrors= foldMap (signatureErrors . syn) signature',
                            moduleEnv= foldMap (Map.singleton (AST.NonQualIdent name) . signatureType . syn) signature',
                            pointerTargets= mempty},
       AST.ForwardDeclaration namedef (Inherited (fst $ inh inherited) <$ signature))

instance Attribution TypeCheck AST.FormalParameters where
   attribution TypeCheck (AST.FormalParameters sections returnType)
               (inherited, AST.FormalParameters sections' _returnType) =
      (Synthesized SynTCSig{signatureErrors= foldMap (sectionErrors . syn) sections' <> foldMap typeRefErrors returnType,
                            signatureType= ProcedureType (foldMap (sectionParameters . syn) sections')
                                           $ returnType >>= (`Map.lookup` env (inh inherited)),
                            signatureEnv= foldMap (sectionEnv . syn) sections'},
       AST.FormalParameters (pure $ Inherited $ inh inherited) returnType)
      where typeRefErrors q
               | Map.member q (env $ inh inherited) = []
               | otherwise = [UnknownName q]

instance Attribution TypeCheck AST.FPSection where
   attribution TypeCheck (AST.FPSection var names _typeDef) (inherited, AST.FPSection _var _names typeDef) =
      (Synthesized SynTCSec{sectionErrors= typeErrors (syn typeDef),
                            sectionParameters= definedType (syn typeDef) <$ toList names,
                            sectionEnv= Map.fromList (toList
                                                      $ flip (,) (definedType $ syn typeDef) . AST.NonQualIdent 
                                                      <$> names)},
       AST.FPSection var names (Inherited $ inh inherited))

instance Attribution TypeCheck AST.Type where
   attribution TypeCheck (AST.TypeReference q) (inherited, _) = 
      (Synthesized SynTCType{typeErrors= if Map.member q (env $ inh inherited) then [] else [UnknownName q],
                             typeName= case q 
                                       of AST.NonQualIdent name -> Just name
                                          _ -> Nothing,
                             pointerTarget= Nothing,
                             definedType= fromMaybe UnknownType (Map.lookup q $ env $ inh inherited)},
       AST.TypeReference q)
   attribution TypeCheck (AST.ArrayType dimensions _itemType) (inherited, AST.ArrayType dimensions' itemType) = 
      (Synthesized SynTCType{typeErrors= foldMap (expressionErrors . syn) dimensions' <> typeErrors (syn itemType)
                                         <> foldMap (expectInteger . syn) dimensions',
                             typeName= Nothing,
                             pointerTarget= Nothing,
                             definedType= ArrayType (integerValue . syn <$> dimensions') (definedType $ syn itemType)},
       AST.ArrayType [Inherited (inh inherited)] (Inherited $ inh inherited))
     where expectInteger SynTCExp{inferredType= NominalType (AST.NonQualIdent "INTEGER") Nothing} = []
           expectInteger SynTCExp{inferredType= t} = [NonIntegerType t]
           integerValue SynTCExp{inferredType= NominalType (AST.NonQualIdent "INTEGER") Nothing} = 0
   attribution TypeCheck (AST.RecordType base fields) (inherited, AST.RecordType _base fields') =
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
                           Just (Just t) -> ([NonRecordType t], Nothing)
                           Just Nothing -> (foldMap ((:[]) . UnknownName) base, Nothing)
                           Nothing -> ([], Nothing)
   attribution TypeCheck _self (inherited, AST.PointerType targetType') =
      (Synthesized SynTCType{typeErrors= typeErrors (syn targetType'),
                             typeName= Nothing,
                             pointerTarget= typeName (syn targetType'),
                             definedType= PointerType (definedType $ syn targetType')},
       AST.PointerType (Inherited $ inh inherited))
   attribution TypeCheck (AST.ProcedureType signature) (inherited, AST.ProcedureType signature') = 
      (Synthesized SynTCType{typeErrors= foldMap (signatureErrors . syn) signature',
                             typeName= Nothing,
                             pointerTarget= Nothing,
                             definedType= maybe (ProcedureType [] Nothing) (signatureType . syn) signature'},
       AST.ProcedureType (Inherited (inh inherited) <$ signature))

instance Attribution TypeCheck AST.FieldList where
   attribution TypeCheck (AST.FieldList names _declaredType) (inherited, AST.FieldList _names declaredType) =
      (Synthesized SynTCFields{fieldErrors= typeErrors (syn declaredType),
                               fieldEnv= foldMap (\name-> Map.singleton (defName name) (definedType $ syn declaredType)) 
                                         names},
       AST.FieldList names (Inherited $ inh inherited))
      where defName (AST.IdentDef name _) = name
   attribution TypeCheck self (inherited, AST.EmptyFieldList) =
     (Synthesized SynTCFields{fieldErrors= [], fieldEnv= mempty},
      AST.EmptyFieldList)

instance Attribution TypeCheck (Deep.Product AST.Expression AST.StatementSequence) where
   attribution TypeCheck self (inherited, Deep.Pair condition statements) =
      (Synthesized SynTC{errors= booleanExpressionErrors (syn condition) <> errors (syn statements)},
       Deep.Pair (Inherited $ inh inherited) (Inherited $ inh inherited))

instance Attribution TypeCheck AST.StatementSequence where
   attribution TypeCheck (AST.StatementSequence statements) (inherited, AST.StatementSequence statements') =
      (Synthesized SynTC{errors= foldMap (errors . syn) statements'},
       AST.StatementSequence (pure $ Inherited $ inh inherited))

instance Attribution TypeCheck AST.Statement where
   attribution TypeCheck self (inherited, AST.EmptyStatement) = (Synthesized SynTC{errors= []}, AST.EmptyStatement)
   attribution TypeCheck self (inherited, AST.Assignment var value) = {-# SCC "Assignment" #-}
      (Synthesized SynTC{errors= typeCompatible (designatorType $ syn var) (inferredType $ syn value)},
       AST.Assignment (Inherited $ inh inherited) (Inherited $ inh inherited))
   attribution TypeCheck (AST.ProcedureCall _proc parameters) (inherited, AST.ProcedureCall procedure' parameters') =
      (Synthesized SynTC{errors= case syn procedure'
                                 of SynTCDes{designatorErrors= [],
                                             designatorType= t} -> {-# SCC "ProcedureCall" #-} procedureErrors t
                                    SynTCDes{designatorErrors= errs} -> errs
                                      <> foldMap (foldMap (expressionErrors . syn)) parameters'},
       AST.ProcedureCall (Inherited $ inh inherited) (Just [Inherited $ inh inherited]))
     where procedureErrors (ProcedureType formalTypes Nothing)
             | length formalTypes /= maybe 0 length parameters =
                 [ArgumentCountMismatch formalTypes $ maybe 0 length parameters]
             | otherwise = concat (zipWith typeCompatible formalTypes $ maybe [] (inferredType . syn <$>) parameters')
           procedureErrors (NominalType _ (Just t)) = procedureErrors t
           procedureErrors t = [NonProcedureType t]
   attribution TypeCheck self (inherited, AST.If branches fallback) =
      (Synthesized SynTC{errors= foldMap (errors . syn) branches <> foldMap (errors . syn) fallback},
       AST.If (pure $ Inherited $ inh inherited) (Inherited (inh inherited) <$ fallback))
   attribution TypeCheck self (inherited, AST.CaseStatement value branches fallback) =
      (Synthesized SynTC{errors= expressionErrors (syn value) <> foldMap (errors . syn) branches
                                 <> foldMap (errors . syn) fallback},
       AST.CaseStatement (Inherited $ inh inherited) (pure $ Inherited $ inh inherited)
                         (Inherited (inh inherited) <$ fallback))
   attribution TypeCheck self (inherited, AST.While condition body) =
      (Synthesized SynTC{errors= booleanExpressionErrors (syn condition) <> errors (syn body)},
       AST.While (Inherited $ inh inherited) (Inherited $ inh inherited))
   attribution TypeCheck self (inherited, AST.Repeat body condition) =
      (Synthesized SynTC{errors= booleanExpressionErrors (syn condition) <> errors (syn body)},
       AST.Repeat (Inherited $ inh inherited) (Inherited $ inh inherited))
   attribution TypeCheck (AST.For counter _start _end _step _body) (inherited, AST.For _counter start end step body) =
      (Synthesized SynTC{errors= integerExpressionErrors (syn start) <> integerExpressionErrors (syn end)
                                 <> foldMap (integerExpressionErrors . syn) step <> errors (syn body)},
       AST.For counter (Inherited $ inh inherited) (Inherited $ inh inherited) (Inherited (inh inherited) <$ step)
                       (Inherited $ InhTC $
                        Map.insert (AST.NonQualIdent counter) (NominalType (AST.NonQualIdent "INTEGER") Nothing)
                        $ env $ inh inherited))
   attribution TypeCheck self (inherited, AST.Loop body) = (Synthesized SynTC{errors= errors (syn body)},
                                                            AST.Loop (Inherited $ inh inherited))
   attribution TypeCheck self (inherited, AST.With branches fallback) =
      (Synthesized SynTC{errors= foldMap (errors . syn) branches <> foldMap (errors . syn) fallback},
       AST.With (pure $ Inherited $ inh inherited) (Inherited (inh inherited) <$ fallback))
   attribution TypeCheck self (inherited, AST.Exit) = (Synthesized SynTC{errors= []}, AST.Exit)
   attribution TypeCheck self (inherited, AST.Return value) =
      (Synthesized SynTC{errors= foldMap (expressionErrors . syn) value}, 
       AST.Return (Inherited (inh inherited) <$ value))

instance Attribution TypeCheck AST.WithAlternative where
   attribution TypeCheck self (inherited, AST.WithAlternative var subtype body) = {-# SCC "WithAlternative" #-}
      (Synthesized SynTC{errors= case (Map.lookup var (env $ inh inherited),
                                       Map.lookup subtype (env $ inh inherited))
                                 of (Just supertype, Just subtypeDef) -> typeCompatible supertype subtypeDef
                                    (Nothing, _) -> [UnknownName var]
                                    (_, Nothing) -> [UnknownName subtype]
                                 <> errors (syn body)},
       AST.WithAlternative var subtype (Inherited $ InhTC $
                                        maybe id (Map.insert var) (Map.lookup subtype $ env $ inh inherited) 
                                        $ env $ inh inherited))

instance Attribution TypeCheck AST.Case where
   attribution TypeCheck self (inherited, AST.Case labels body) =
      (Synthesized SynTC{errors= foldMap (errors . syn) labels <> errors (syn body)},
       AST.Case (pure $ Inherited $ inh inherited) (Inherited $ inh inherited))
   attribution TypeCheck self (inherited, AST.EmptyCase) = (Synthesized SynTC{errors= []}, AST.EmptyCase)

instance Attribution TypeCheck AST.CaseLabels where
   attribution TypeCheck self (inherited, AST.SingleLabel value) =
      (Synthesized SynTC{errors= integerExpressionErrors (syn value)},
       AST.SingleLabel (Inherited $ inh inherited))
   attribution TypeCheck self (inherited, AST.LabelRange start end) =
      (Synthesized SynTC{errors= integerExpressionErrors (syn start) <> integerExpressionErrors (syn end)},
       AST.LabelRange (Inherited $ inh inherited) (Inherited $ inh inherited))

instance Attribution TypeCheck AST.Expression where
   attribution TypeCheck self (inherited, AST.Relation op left right) =
      (Synthesized SynTCExp{expressionErrors= case expressionErrors (syn left) <> expressionErrors (syn right)
                                              of [] | inferredType (syn left) == inferredType (syn right) -> []
                                                    | otherwise -> [TypeMismatch
                                                                     (inferredType $ syn left)
                                                                     (inferredType $ syn right)]
                                                 errs -> errs,
                            inferredType= NominalType (AST.NonQualIdent "BOOLEAN") Nothing},
       AST.Relation op (Inherited $ inh inherited) (Inherited $ inh inherited))
   attribution TypeCheck self (inherited, AST.Positive expr) =
      (Synthesized SynTCExp{expressionErrors= unaryNumericOperatorErrors (syn expr),
                            inferredType= inferredType (syn expr)},
       AST.Positive (Inherited $ inh inherited))
   attribution TypeCheck self (inherited, AST.Negative expr) = 
      (Synthesized SynTCExp{expressionErrors= unaryNumericOperatorErrors (syn expr),
                            inferredType= inferredType (syn expr)},
       AST.Negative (Inherited $ inh inherited))
   attribution TypeCheck self (inherited, AST.Add left right) =
      (Synthesized SynTCExp{expressionErrors= binaryNumericOperatorErrors (syn left) (syn right),
                            inferredType= inferredType (syn left)},
       AST.Add (Inherited $ inh inherited) (Inherited $ inh inherited))
   attribution TypeCheck self (inherited, AST.Subtract left right) =
      (Synthesized SynTCExp{expressionErrors= binaryNumericOperatorErrors (syn left) (syn right),
                            inferredType= inferredType (syn left)},
       AST.Subtract (Inherited $ inh inherited) (Inherited $ inh inherited))
   attribution TypeCheck self (inherited, AST.Or left right) =
      (Synthesized SynTCExp{expressionErrors= binaryBooleanOperatorErrors (syn left) (syn right),
                            inferredType= NominalType (AST.NonQualIdent "BOOLEAN") Nothing},
       AST.Or (Inherited $ inh inherited) (Inherited $ inh inherited))
   attribution TypeCheck self (inherited, AST.Multiply left right) =
      (Synthesized SynTCExp{expressionErrors= binaryNumericOperatorErrors (syn left) (syn right),
                            inferredType= inferredType (syn left)},
       AST.Multiply (Inherited $ inh inherited) (Inherited $ inh inherited))
   attribution TypeCheck self (inherited, AST.Divide left right) =
      (Synthesized SynTCExp{expressionErrors=
                               case (syn left, syn right)
                               of (SynTCExp{expressionErrors= [],
                                            inferredType= NominalType (AST.NonQualIdent "REAL") Nothing},
                                   SynTCExp{expressionErrors= [],
                                            inferredType= NominalType (AST.NonQualIdent "REAL") Nothing}) -> []
                                  (SynTCExp{expressionErrors= [], inferredType= t1},
                                   SynTCExp{expressionErrors= [], inferredType= t2})
                                    | t1 == t2 -> [UnrealType t1]
                                    | otherwise -> [TypeMismatch t1 t2],
                            inferredType= NominalType (AST.NonQualIdent "REAL") Nothing},
       AST.Divide (Inherited $ inh inherited) (Inherited $ inh inherited))
   attribution TypeCheck self (inherited, AST.IntegerDivide left right) =
      (Synthesized SynTCExp{expressionErrors= binaryIntegerOperatorErrors (syn left) (syn right),
                            inferredType= NominalType (AST.NonQualIdent "INTEGER") Nothing},
       AST.IntegerDivide (Inherited $ inh inherited) (Inherited $ inh inherited))
   attribution TypeCheck self (inherited, AST.Modulo left right) =
      (Synthesized SynTCExp{expressionErrors= binaryIntegerOperatorErrors (syn left) (syn right),
                            inferredType= NominalType (AST.NonQualIdent "INTEGER") Nothing},
        AST.Modulo (Inherited $ inh inherited) (Inherited $ inh inherited))
   attribution TypeCheck self (inherited, AST.And left right) =
      (Synthesized SynTCExp{expressionErrors= binaryBooleanOperatorErrors (syn left) (syn right),
                            inferredType= NominalType (AST.NonQualIdent "BOOLEAN") Nothing},
       AST.And (Inherited $ inh inherited) (Inherited $ inh inherited))
   attribution TypeCheck self (inherited, AST.Integer x) =
      (Synthesized SynTCExp{expressionErrors= mempty,
                            inferredType= NominalType (AST.NonQualIdent "INTEGER") Nothing},
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
   attribution TypeCheck self (inherited, AST.String x) =
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
   attribution TypeCheck (AST.FunctionCall _designator parameters)
               (inherited, AST.FunctionCall designator parameters') =
      (Synthesized SynTCExp{expressionErrors= case {-# SCC "FunctionCall" #-} syn designator
                                              of SynTCDes{designatorErrors= [],
                                                          designatorType= ProcedureType formalTypes Just{}}
                                                   | length formalTypes /= length parameters ->
                                                       [ArgumentCountMismatch formalTypes (length parameters)]
                                                   | otherwise -> concat (zipWith typeCompatible formalTypes $
                                                                          inferredType . syn <$> parameters')
                                                 SynTCDes{designatorErrors= [],
                                                          designatorType= t} -> [NonFunctionType t]
                                                 SynTCDes{designatorErrors= errs} -> errs
                                              <> foldMap (expressionErrors . syn) parameters',
                            inferredType= case syn designator
                                          of SynTCDes{designatorType= ProcedureType _ (Just returnType)} -> returnType
                                             _ -> UnknownType},
       AST.FunctionCall (Inherited $ inh inherited) [Inherited $ inh inherited])
   attribution TypeCheck self (inherited, AST.Not expr) =
      (Synthesized SynTCExp{expressionErrors= booleanExpressionErrors (syn expr),
                            inferredType= NominalType (AST.NonQualIdent "BOOLEAN") Nothing},
       AST.Not (Inherited $ inh inherited))

instance Attribution TypeCheck AST.Element where
   attribution TypeCheck self (inherited, AST.Element expr) =
      (Synthesized SynTCExp{expressionErrors= case expressionErrors (syn expr)
                                              of [] | inferredType (syn expr) 
                                                      == NominalType (AST.NonQualIdent "INTEGER") Nothing -> []
                                                    | otherwise -> [NonIntegerType (inferredType $ syn expr)]
                                                 errs -> errs,
                            inferredType= NominalType (AST.NonQualIdent "SET") Nothing},
       AST.Element (Inherited $ inh inherited))
   attribution TypeCheck self (inherited, AST.Range low high) =
      (Synthesized SynTCExp{expressionErrors=
                               case (syn low, syn high)
                               of (SynTCExp{expressionErrors= [],
                                            inferredType= NominalType (AST.NonQualIdent "INTEGER") Nothing},
                                   SynTCExp{expressionErrors= [],
                                            inferredType= NominalType (AST.NonQualIdent "INTEGER") Nothing}) 
                                     -> []
                                  (SynTCExp{expressionErrors= [], inferredType= t1},
                                   SynTCExp{expressionErrors= [], inferredType= t2})
                                     | t1 /= t2 -> [TypeMismatch t1 t2]
                                     | otherwise -> [NonIntegerType t1]
                                  (SynTCExp{expressionErrors= errors1}, 
                                   SynTCExp{expressionErrors= errors2}) -> errors1 <> errors2,
                            inferredType= NominalType (AST.NonQualIdent "SET") Nothing},
       AST.Range (Inherited $ inh inherited) (Inherited $ inh inherited))

instance Attribution TypeCheck AST.Designator where
   attribution TypeCheck (AST.Variable q) (inherited, _) =
      (Synthesized SynTCDes{designatorErrors= case designatorType
                                              of Nothing -> [UnknownName q]
                                                 Just{} -> [],
                            designatorSelf= AST.Variable q,
                            designatorType= fromMaybe UnknownType designatorType},
       AST.Variable q)
      where designatorType = Map.lookup q (env $ inh inherited)
   attribution TypeCheck (AST.Field _record fieldName) (inherited, AST.Field record _fieldName) =
      (Synthesized SynTCDes{designatorErrors= case syn record
                                              of SynTCDes{designatorErrors= [],
                                                          designatorType= t} ->
                                                   maybe [NonRecordType t]
                                                         (maybe [UnknownField fieldName t] $ const []) (access True t)
                                                 SynTCDes{designatorErrors= errors} -> errors,
                            designatorSelf= AST.Field (Identity $ designatorSelf $ syn record) fieldName,
                            designatorType= fromMaybe UnknownType (fromMaybe Nothing $ access True
                                                                   $ designatorType $ syn record)},
       AST.Field (Inherited $ inh inherited) fieldName)
     where access _ (RecordType _ fields) = Just (Map.lookup fieldName fields)
           access True (PointerType t) = access False t
           access allowPtr (NominalType _ (Just t)) = access allowPtr t
           access _ _ = Nothing
   attribution TypeCheck (AST.Index _array indexes) (inherited, AST.Index array _indexes) =
      (Synthesized SynTCDes{designatorErrors= case syn array
                                              of SynTCDes{designatorErrors= [],
                                                          designatorType= t@(ArrayType dimensions _)}
                                                    | length dimensions == length indexes -> []
                                                    | length dimensions == 0 && length indexes == 1 -> []
                                                    | otherwise -> [ExtraDimensionalIndex t]
                                                 SynTCDes{designatorErrors= [],
                                                          designatorType= t} -> [NonArrayType t]
                                                 SynTCDes{designatorErrors= errors} -> errors,
                            designatorType= case designatorType (syn array)
                                            of ArrayType _ itemType -> itemType
                                               _ -> UnknownType},
       AST.Index (Inherited $ inh inherited) (pure $ Inherited $ inh inherited))
   attribution TypeCheck self (inherited, AST.TypeGuard designator q) = {-# SCC "TypeGuard" #-}
      (Synthesized SynTCDes{designatorErrors= case (syn designator, targetType)
                                              of (SynTCDes{designatorErrors= [],
                                                           designatorType= t}, 
                                                  Just t') -> typeCompatible t' t
                                                 (SynTCDes{designatorErrors= errors}, 
                                                  Nothing) -> UnknownName q : errors
                                                 (SynTCDes{designatorErrors= errors}, _) -> errors,
                            designatorType= fromMaybe UnknownType targetType},
       AST.TypeGuard (Inherited $ inh inherited) q)
      where targetType = Map.lookup q (env $ inh inherited)
   attribution TypeCheck self (inherited, AST.Dereference pointer) =
      (Synthesized SynTCDes{designatorErrors= case syn pointer
                                              of SynTCDes{designatorErrors= [],
                                                          designatorType= PointerType{}} -> []
                                                 SynTCDes{designatorErrors= [],
                                                          designatorType= NominalType _ (Just PointerType{})} -> []
                                                 SynTCDes{designatorErrors= [],
                                                          designatorType= t} -> [NonPointerType t]
                                                 SynTCDes{designatorErrors= errors} -> errors,
                            designatorType= case designatorType (syn pointer)
                                            of NominalType _ (Just (PointerType t)) -> t
                                               PointerType t -> t
                                               _ -> UnknownType},
       AST.Dereference (Inherited $ inh inherited))

unaryNumericOperatorErrors :: SynTCExp -> [Error]
unaryNumericOperatorErrors SynTCExp{expressionErrors= [],
                                    inferredType= NominalType (AST.NonQualIdent "REAL") Nothing} = []
unaryNumericOperatorErrors SynTCExp{expressionErrors= [],
                                    inferredType= NominalType (AST.NonQualIdent "INTEGER") Nothing} = []
unaryNumericOperatorErrors SynTCExp{expressionErrors= [], inferredType= t} = [NonNumericType t]
unaryNumericOperatorErrors SynTCExp{expressionErrors= errs} = errs

binaryNumericOperatorErrors :: SynTCExp -> SynTCExp -> [Error]
binaryNumericOperatorErrors
  SynTCExp{expressionErrors= [], inferredType= NominalType (AST.NonQualIdent "REAL") Nothing}
  SynTCExp{expressionErrors= [], inferredType= NominalType (AST.NonQualIdent "REAL") Nothing} = []
binaryNumericOperatorErrors
  SynTCExp{expressionErrors= [], inferredType= NominalType (AST.NonQualIdent "INTEGER") Nothing}
  SynTCExp{expressionErrors= [], inferredType= NominalType (AST.NonQualIdent "INTEGER") Nothing} = []
binaryNumericOperatorErrors SynTCExp{expressionErrors= [], inferredType= t1}
                            SynTCExp{expressionErrors= [], inferredType= t2}
  | t1 == t2 = [NonNumericType t1]
  | otherwise = [TypeMismatch t1 t2]
binaryNumericOperatorErrors SynTCExp{expressionErrors= errs1} SynTCExp{expressionErrors= errs2} = errs1 <> errs2

binaryIntegerOperatorErrors :: SynTCExp -> SynTCExp -> [Error]
binaryIntegerOperatorErrors
  SynTCExp{expressionErrors= [], inferredType= NominalType (AST.NonQualIdent "INTEGER") Nothing}
  SynTCExp{expressionErrors= [], inferredType= NominalType (AST.NonQualIdent "INTEGER") Nothing} = []
binaryIntegerOperatorErrors SynTCExp{expressionErrors= [], inferredType= t1}
                            SynTCExp{expressionErrors= [], inferredType= t2}
  | t1 == t2 = [NonIntegerType t1]
  | otherwise = [TypeMismatch t1 t2]

integerExpressionErrors SynTCExp{expressionErrors= [],
                                 inferredType= NominalType (AST.NonQualIdent "INTEGER") Nothing} = []
integerExpressionErrors SynTCExp{expressionErrors= [], inferredType= t} = [NonIntegerType t]
integerExpressionErrors SynTCExp{expressionErrors= errs} = errs

booleanExpressionErrors SynTCExp{expressionErrors= [],
                                 inferredType= NominalType (AST.NonQualIdent "BOOLEAN") Nothing} = []
booleanExpressionErrors SynTCExp{expressionErrors= [], inferredType= t} = [NonBooleanType t]
booleanExpressionErrors SynTCExp{expressionErrors= errs} = errs

binaryBooleanOperatorErrors :: SynTCExp -> SynTCExp -> [Error]
binaryBooleanOperatorErrors
  SynTCExp{expressionErrors= [], inferredType= NominalType (AST.NonQualIdent "BOOLEAN") Nothing}
  SynTCExp{expressionErrors= [], inferredType= NominalType (AST.NonQualIdent "BOOLEAN") Nothing} = []
binaryBooleanOperatorErrors SynTCExp{expressionErrors= [], inferredType= t1}
                            SynTCExp{expressionErrors= [], inferredType= t2}
  | t1 == t2 = [NonBooleanType t1]
  | otherwise = [TypeMismatch t1 t2]

typeCompatible :: Type -> Type -> [Error]
typeCompatible expected actual
   | expected == actual = []
   | expected == NominalType (AST.NonQualIdent "BASIC TYPE") Nothing,
     NominalType (AST.NonQualIdent q) Nothing <- actual,
     q `elem` ["BOOLEAN", "CHAR", "SHORTINT", "INTEGER", "LONGINT", "REAL", "LONGREAL", "SET"] = []
   | expected == NominalType (AST.NonQualIdent "POINTER") Nothing, PointerType{} <- actual = []
   | expected == NominalType (AST.NonQualIdent "POINTER") Nothing, NominalType _ (Just t) <- actual =
       typeCompatible expected t
   | NilType <- actual, PointerType{} <- expected = []
   | NilType <- actual, ProcedureType{} <- expected = []
   | NilType <- actual, NominalType _ (Just t) <- expected = typeCompatible t actual
   | ArrayType [] (NominalType (AST.NonQualIdent "CHAR") Nothing) <- expected, StringType{} <- actual = []
   | targetExtends actual expected = []
   | NominalType _ (Just t) <- expected, ProcedureType{} <- actual = typeCompatible t actual
   | otherwise = error (show (expected, actual))

extends, targetExtends :: Type -> Type -> Bool
t1 `extends` t2 | t1 == t2 = True
RecordType ancestry _ `extends` NominalType q _ = q `elem` ancestry
NominalType _ (Just t1) `extends` t2 = t1 `extends` t2
t1 `extends` t2 = error (show (t1, t2))

PointerType t1 `targetExtends` PointerType t2 = t1 `extends` t2
NominalType _ (Just t1) `targetExtends` t2 = t1 `targetExtends` t2
t1 `targetExtends` NominalType _ (Just t2) = t1 `targetExtends` t2
t1 `targetExtends` t2 | t1 == t2 = True
t1 `targetExtends` t2 = False

anonymize :: Type -> Type
anonymize (RecordType ancestry fields) = RecordType ancestry (NominalType (AST.NonQualIdent "?") Nothing <$ fields)
anonymize (ArrayType dimensions itemType) = ArrayType dimensions (anonymize itemType)
anonymize (PointerType targetType) = PointerType (anonymize targetType)
anonymize (ProcedureType params result) = ProcedureType (anonymize <$> params) (anonymize <$> result)
anonymize (NominalType n (Just t)) = NominalType n (Just $ anonymize t)
anonymize t = t

-- * More boring Shallow.Functor instances, TH candidates
instance Shallow.Functor TypeCheck Identity (Semantics TypeCheck)
         (Modules (Semantics TypeCheck) (Semantics TypeCheck)) where
   (<$>) = AG.mapDefault
instance Shallow.Functor TypeCheck Identity (Semantics TypeCheck)
         (AST.Module (Semantics TypeCheck) (Semantics TypeCheck)) where
   (<$>) = AG.mapDefault
instance Shallow.Functor TypeCheck Identity (Semantics TypeCheck)
         (AST.Declaration (Semantics TypeCheck) (Semantics TypeCheck)) where
   (<$>) = AG.mapDefault
instance Shallow.Functor TypeCheck Identity (Semantics TypeCheck)
         (AST.FormalParameters (Semantics TypeCheck) (Semantics TypeCheck)) where
   (<$>) = AG.mapDefault
instance Shallow.Functor TypeCheck Identity (Semantics TypeCheck)
         (AST.FPSection (Semantics TypeCheck) (Semantics TypeCheck)) where
   (<$>) = AG.mapDefault
instance Shallow.Functor TypeCheck Identity (Semantics TypeCheck)
         (Deep.Product AST.Expression AST.StatementSequence (Semantics TypeCheck) (Semantics TypeCheck)) where
   (<$>) = AG.mapDefault
instance Shallow.Functor TypeCheck Identity (Semantics TypeCheck)
         (AST.StatementSequence (Semantics TypeCheck) (Semantics TypeCheck)) where
   (<$>) = AG.mapDefault
instance Shallow.Functor TypeCheck Identity (Semantics TypeCheck)
         (AST.Statement (Semantics TypeCheck) (Semantics TypeCheck)) where
   (<$>) = AG.mapDefault
instance Shallow.Functor TypeCheck Identity (Semantics TypeCheck)
         (AST.Case (Semantics TypeCheck) (Semantics TypeCheck)) where
   (<$>) = AG.mapDefault
instance Shallow.Functor TypeCheck Identity (Semantics TypeCheck)
         (AST.CaseLabels (Semantics TypeCheck) (Semantics TypeCheck)) where
   (<$>) = AG.mapDefault
instance Shallow.Functor TypeCheck Identity (Semantics TypeCheck)
         (AST.WithAlternative (Semantics TypeCheck) (Semantics TypeCheck)) where
   (<$>) = AG.mapDefault
instance Shallow.Functor TypeCheck Identity (Semantics TypeCheck)
         (AST.Expression (Semantics TypeCheck) (Semantics TypeCheck)) where
   (<$>) = AG.mapDefault
instance Shallow.Functor TypeCheck Identity (Semantics TypeCheck)
         (AST.Element (Semantics TypeCheck) (Semantics TypeCheck)) where
   (<$>) = AG.mapDefault
instance Shallow.Functor TypeCheck Identity (Semantics TypeCheck)
         (AST.Designator (Semantics TypeCheck) (Semantics TypeCheck)) where
   (<$>) = AG.mapDefault
instance Shallow.Functor TypeCheck Identity (Semantics TypeCheck)
         (AST.Type (Semantics TypeCheck) (Semantics TypeCheck)) where
   (<$>) = AG.mapDefault
instance Shallow.Functor TypeCheck Identity (Semantics TypeCheck)
         (AST.FieldList (Semantics TypeCheck) (Semantics TypeCheck)) where
   (<$>) = AG.mapDefault

-- * Unsafe Rank2 AST instances

instance Rank2.Apply (AST.Module f') where
   AST.Module ident1a imports1 decls1 body1 ident1b <*> ~(AST.Module ident2a imports2 decls2 body2 ident2b) =
      AST.Module ident1a imports1 (liftA2 Rank2.apply decls1 decls2) (liftA2 Rank2.apply body1 body2) ident1b

checkModules :: Environment -> Map AST.Ident (AST.Module Identity Identity) -> [Error]
checkModules predef modules = 
   errors (syn (TypeCheck Shallow.<$> Identity (TypeCheck Deep.<$> Modules (Identity <$> modules))
                `Rank2.apply`
                Inherited (InhTC predef)))

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
    ("ABS", ProcedureType [NominalType (AST.NonQualIdent "INTEGER") Nothing] $
            Just $ NominalType (AST.NonQualIdent "INTEGER") Nothing),
    ("ASH", ProcedureType [NominalType (AST.NonQualIdent "INTEGER") Nothing] $
            Just $ NominalType (AST.NonQualIdent "INTEGER") Nothing),
    ("CAP", ProcedureType [NominalType (AST.NonQualIdent "INTEGER") Nothing] $
            Just $ NominalType (AST.NonQualIdent "CAP") Nothing),
    ("LEN", ProcedureType [NominalType (AST.NonQualIdent "ARRAY") Nothing] $
            Just $ NominalType (AST.NonQualIdent "LONGINT") Nothing),
    ("MAX", ProcedureType [NominalType (AST.NonQualIdent "BASIC TYPE") Nothing] $
            Just $ NominalType (AST.NonQualIdent "INTEGER") Nothing),
    ("MIN", ProcedureType [NominalType (AST.NonQualIdent "BASIC TYPE") Nothing] $
            Just $ NominalType (AST.NonQualIdent "INTEGER") Nothing),
    ("ODD", ProcedureType [NominalType (AST.NonQualIdent "CHAR") Nothing] $
            Just $ NominalType (AST.NonQualIdent "BOOLEAN") Nothing),
    ("SIZE", ProcedureType [NominalType (AST.NonQualIdent "CHAR") Nothing] $
             Just $ NominalType (AST.NonQualIdent "INTEGER") Nothing),
    ("ORD", ProcedureType [NominalType (AST.NonQualIdent "CHAR") Nothing] $
            Just $ NominalType (AST.NonQualIdent "INTEGER") Nothing),
    ("CHR", ProcedureType [NominalType (AST.NonQualIdent "INTEGER") Nothing] $
            Just $ NominalType (AST.NonQualIdent "CHAR") Nothing),
    ("SHORT", ProcedureType [NominalType (AST.NonQualIdent "INTEGER") Nothing]
              $ Just $ NominalType (AST.NonQualIdent "INTEGER") Nothing),
    ("LONG", ProcedureType [NominalType (AST.NonQualIdent "INTEGER") Nothing] $
             Just $ NominalType (AST.NonQualIdent "INTEGER") Nothing),
    ("ENTIER", ProcedureType [NominalType (AST.NonQualIdent "REAL") Nothing] $
               Just $ NominalType (AST.NonQualIdent "INTEGER") Nothing),
    ("INC", ProcedureType [NominalType (AST.NonQualIdent "INTEGER") Nothing] Nothing),
    ("DEC", ProcedureType [NominalType (AST.NonQualIdent "INTEGER") Nothing] Nothing),
    ("INCL", ProcedureType [NominalType (AST.NonQualIdent "SET") Nothing,
                            NominalType (AST.NonQualIdent "INTEGER") Nothing] Nothing),
    ("EXCL", ProcedureType [NominalType (AST.NonQualIdent "SET") Nothing,
                            NominalType (AST.NonQualIdent "INTEGER") Nothing] Nothing),
    ("COPY", ProcedureType [NominalType (AST.NonQualIdent "ARRAY") Nothing,
                            NominalType (AST.NonQualIdent "ARRAY") Nothing] Nothing),
    ("NEW", ProcedureType [NominalType (AST.NonQualIdent "POINTER") Nothing] Nothing),
    ("HALT", ProcedureType [NominalType (AST.NonQualIdent "INTEGER") Nothing] Nothing)]

-- | The set of 'Predefined' types and procedures defined in the Oberon-2 Language Report.
predefined2 = predefined <>
   Map.fromList (first AST.NonQualIdent <$>
                 [("ASSERT", ProcedureType [NominalType (AST.NonQualIdent "ARRAY") Nothing,
                                            NominalType (AST.NonQualIdent "ARRAY") Nothing] Nothing)])

$(mconcat <$> mapM Rank2.TH.unsafeDeriveApply
  [''AST.Declaration, ''AST.Type, ''AST.Expression,
   ''AST.Element, ''AST.Designator, ''AST.FieldList,
   ''AST.ProcedureHeading, ''AST.FormalParameters, ''AST.FPSection, ''AST.ProcedureBody,
   ''AST.Statement, ''AST.StatementSequence, ''AST.WithAlternative, ''AST.Case, ''AST.CaseLabels])
