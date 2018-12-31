{-# LANGUAGE FlexibleContexts, FlexibleInstances, MultiParamTypeClasses, OverloadedStrings,
             TemplateHaskell, TypeFamilies, UndecidableInstances #-}

module Language.Oberon.TypeChecker (Error(..), checkModules) where

import Control.Applicative (liftA2)
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

data Type = NominalType AST.QualIdent
          | RecordType{ancestry :: [AST.QualIdent],
                       recordFields :: Map AST.Ident Type}
          | NilType
          | StringType Int
          | ArrayType [Int] Type
          | PointerType Type
          | ProcedureType [Type] (Maybe Type)
          | UnknownType
          deriving (Eq, Show)

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
           | UnknownField AST.Ident
           deriving Show

type Environment = Map AST.QualIdent Type

newtype Modules f' f = Modules (Map AST.Ident (f (AST.Module f' f')))

data TypeCheck = TypeCheck

data InhTC = InhTC{env :: Environment} deriving Show

data SynTC = SynTC{errors :: [Error]} deriving Show

data SynTC' = SynTC'{errors' :: [Error],
                     env' :: Environment} deriving Show

data SynTCType = SynTCType{typeErrors :: [Error],
                           definedType :: Type} deriving Show

data SynTCFields = SynTCFields{fieldErrors :: [Error],
                               fieldEnv :: Map AST.Ident Type} deriving Show

data SynTCSig = SynTCSig{signatureErrors :: [Error],
                         signatureEnv :: Environment,
                         signatureType :: Type} deriving Show

data SynTCSec = SynTCSec{sectionErrors :: [Error],
                         sectionEnv :: Environment,
                         sectionParameters :: [Type]} deriving Show

data SynTCDes = SynTCDes{designatorErrors :: [Error],
                         designatorType :: Type} deriving Show

data SynTCExp = SynTCExp{expressionErrors :: [Error],
                         inferredType :: Type} deriving Show

-- * Modules instances, TH candidates
instance (Functor p, Deep.Functor t AST.Module p q, Shallow.Functor t p q (AST.Module q q)) =>
         Deep.Functor t Modules p q where
   t <$> Modules ms = Modules (mapModule <$> ms)
      where mapModule m = t Shallow.<$> ((t Deep.<$>) <$> m)

instance Rank2.Functor (Modules f') where
   f <$> Modules ms = Modules (f <$> ms)

instance Rank2.Apply (Modules f') where
   Modules fs <*> Modules ms = Modules (Map.intersectionWith Rank2.apply fs ms)

-- * Boring attribute types
type instance Atts (Inherited TypeCheck) (Modules f' f) = InhTC
type instance Atts (Synthesized TypeCheck) (Modules f' f) = SynTC
type instance Atts (Inherited TypeCheck) (AST.Module f' f) = InhTC
type instance Atts (Synthesized TypeCheck) (AST.Module f' f) = SynTC'
type instance Atts (Inherited TypeCheck) (AST.Declaration f' f) = InhTC
type instance Atts (Synthesized TypeCheck) (AST.Declaration f' f) = SynTC'
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
   attribution TypeCheck (inherited, Modules ms) = (Synthesized SynTC{errors= foldMap (errors' . syn) ms},
                                                    Modules (inherited' <$ ms))
      where inherited' = Inherited InhTC{env= env (inh inherited) <> foldMap (env' . syn) ms}

instance Attribution TypeCheck AST.Module where
   attribution TypeCheck (inherited, AST.Module ident1 imports decls body ident2) =
      (Synthesized SynTC'{errors'= foldMap (errors' . syn) decls <> foldMap (errors . syn) body,
                          env'= foldMap (env' . syn) decls},
       AST.Module ident1 imports (Inherited (inh inherited) <$ decls) (Inherited (inh inherited) <$ body) ident2)


instance Attribution TypeCheck AST.Declaration where
   attribution TypeCheck (inherited, AST.ConstantDeclaration namedef@(AST.IdentDef name _) expression) =
      (Synthesized SynTC'{errors'= errorIfDuplicate (env $ inh inherited) name <> expressionErrors (syn expression),
                          env'= Map.insert (AST.NonQualIdent name) (inferredType $ syn expression) 
                                $ env $ inh inherited},
       AST.ConstantDeclaration namedef (Inherited $ inh inherited))
   attribution TypeCheck (inherited, AST.TypeDeclaration namedef@(AST.IdentDef name _) definition) =
      (Synthesized SynTC'{errors'= errorIfDuplicate (env $ inh inherited) name <> typeErrors (syn definition),
                          env'= Map.insert (AST.NonQualIdent name) (definedType $ syn definition) 
                                $ env $ inh inherited},
       AST.TypeDeclaration namedef (Inherited $ inh inherited))
   attribution TypeCheck (inherited, AST.VariableDeclaration names declaredType) =
      (Synthesized SynTC'{errors'= foldMap (errorIfDuplicate (env $ inh inherited) . defName) names 
                                   <> typeErrors (syn declaredType),
                          env'= foldr (\name-> Map.insert (AST.NonQualIdent $ defName name)
                                               (definedType $ syn declaredType))
                                      (env $ inh inherited)
                                      names},
       AST.VariableDeclaration names (Inherited $ inh inherited))
      where defName (AST.IdentDef name _) = name
   attribution TypeCheck (inherited,
                          AST.ProcedureDeclaration h@(AST.ProcedureHeading receiver indirect 
                                                      namedef@(AST.IdentDef name _) signature) 
                                                   body@(AST.ProcedureBody declarations statements) name') =
      (Synthesized SynTC'{errors'= errorIfDuplicate (env $ inh inherited) name 
                                   <> foldMap (signatureErrors . syn) signature,
                          env'= foldMap (Map.singleton (AST.NonQualIdent name) . signatureType . syn) signature
                                <> env (inh inherited)},
       AST.ProcedureDeclaration 
          (AST.ProcedureHeading receiver indirect namedef (Inherited (inh inherited) <$ signature))
          (AST.ProcedureBody (Inherited localInherited <$ declarations) (Inherited localInherited <$ statements))
          name')
     where receiverEnv (_, formalName, typeName) =
             foldMap (Map.singleton $ AST.NonQualIdent formalName) (Map.lookup (AST.NonQualIdent typeName) 
                                                                    $ env $ inh inherited)
           receiverError (_, formalName, typeName) =
             case Map.lookup (AST.NonQualIdent typeName) (env $ inh inherited)
             of Nothing -> [UnknownName $ AST.NonQualIdent typeName]
                Just RecordType{} -> []
                Just t -> [NonRecordType t]
           localInherited = InhTC (foldMap receiverEnv receiver
                                   `Map.union` foldMap (signatureEnv . syn) signature
                                   `Map.union` env (inh inherited))
   attribution TypeCheck (inherited, AST.ForwardDeclaration namedef@(AST.IdentDef name _) signature) =
      (Synthesized SynTC'{errors'= errorIfDuplicate (env $ inh inherited) name
                                   <> foldMap (signatureErrors . syn) signature,
                          env'= foldMap (Map.singleton (AST.NonQualIdent name) . signatureType . syn) signature
                                <> env (inh inherited)},
       AST.ForwardDeclaration namedef (Inherited (inh inherited) <$ signature))

instance Attribution TypeCheck AST.FormalParameters where
   attribution TypeCheck (inherited, AST.FormalParameters sections returnType) =
      (Synthesized SynTCSig{signatureErrors= foldMap (sectionErrors . syn) sections <> foldMap typeRefErrors returnType,
                            signatureType= ProcedureType (foldMap (sectionParameters . syn) sections)
                                           $ returnType >>= (`Map.lookup` env (inh inherited)) ,
                            signatureEnv= foldMap (sectionEnv . syn) sections},
       AST.FormalParameters (Inherited (inh inherited) <$ sections) returnType)
      where typeRefErrors q
               | Map.member q (env $ inh inherited) = []
               | otherwise = [UnknownName q]

instance Attribution TypeCheck AST.FPSection where
   attribution TypeCheck (inherited, AST.FPSection var names typeDef) =
      (Synthesized SynTCSec{sectionErrors= typeErrors (syn typeDef),
                            sectionParameters= definedType (syn typeDef) <$ toList names,
                            sectionEnv= Map.fromList (toList 
                                                      $ flip (,) (definedType $ syn typeDef) . AST.NonQualIdent 
                                                      <$> names)},
       AST.FPSection var names (Inherited $ inh inherited))

instance Attribution TypeCheck AST.Type where
   attribution TypeCheck (inherited, AST.TypeReference q) = 
      (Synthesized SynTCType{typeErrors= if Map.member q (env $ inh inherited) then [] else [UnknownName q],
                             definedType= fromMaybe UnknownType (Map.lookup q $ env $ inh inherited)},
       AST.TypeReference q)
   attribution TypeCheck (inherited, AST.ArrayType dimensions itemType) = 
      (Synthesized SynTCType{typeErrors= foldMap (expressionErrors . syn) dimensions <> typeErrors (syn itemType)
                                         <> foldMap (expectInteger . syn) dimensions,
                             definedType= ArrayType (integerValue . syn <$> dimensions) (definedType $ syn itemType)},
       AST.ArrayType (Inherited (inh inherited) <$ dimensions) (Inherited $ inh inherited))
     where expectInteger SynTCExp{inferredType= NominalType (AST.NonQualIdent "INTEGER")} = []
           expectInteger SynTCExp{inferredType= t} = [NonIntegerType t]
           integerValue SynTCExp{inferredType= NominalType (AST.NonQualIdent "INTEGER")} = 0
   attribution TypeCheck (inherited, AST.RecordType base fields) = 
      (Synthesized SynTCType{typeErrors= fst baseRecord <> foldMap (fieldErrors . syn) fields,
                             definedType= RecordType (maybe [] (maybe id (:) base . ancestry) $ snd baseRecord)
                                             (maybe Map.empty recordFields (snd baseRecord)
                                              <> foldMap (fieldEnv . syn) fields)},
       AST.RecordType base (Inherited (inh inherited) <$ fields))
     where baseRecord = case flip Map.lookup (env $ inh inherited) <$> base
                        of Just (Just t@RecordType{}) -> ([], Just t)
                           Just (Just t) -> ([NonRecordType t], Nothing)
                           Just Nothing -> (foldMap ((:[]) . UnknownName) base, Nothing)
                           Nothing -> ([], Nothing)
   attribution TypeCheck (inherited, AST.PointerType targetType) = 
      (Synthesized SynTCType{typeErrors= typeErrors (syn targetType),
                             definedType= definedType (syn targetType)},
       AST.PointerType (Inherited $ inh inherited))
   attribution TypeCheck (inherited, AST.ProcedureType signature) = 
      (Synthesized SynTCType{typeErrors= foldMap (signatureErrors . syn) signature,
                             definedType= maybe (ProcedureType [] Nothing) (signatureType . syn) signature},
       AST.ProcedureType (Inherited (inh inherited) <$ signature))

instance Attribution TypeCheck AST.FieldList where
   attribution TypeCheck (inherited, AST.FieldList names declaredType) =
      (Synthesized SynTCFields{fieldErrors= typeErrors (syn declaredType),
                               fieldEnv= foldr (\name-> Map.insert (defName name) (definedType $ syn declaredType))
                                               mempty
                                               names},
       AST.FieldList names (Inherited $ inh inherited))
      where defName (AST.IdentDef name _) = name
   attribution TypeCheck (inherited, AST.EmptyFieldList) = (Synthesized SynTCFields{fieldErrors= [], fieldEnv= mempty},
                                                            AST.EmptyFieldList)

instance Attribution TypeCheck (Deep.Product AST.Expression AST.StatementSequence) where
   attribution TypeCheck (inherited, Deep.Pair condition statements) =
      (Synthesized SynTC{errors= booleanExpressionErrors (syn condition) <> errors (syn statements)},
       Deep.Pair (Inherited $ inh inherited) (Inherited $ inh inherited))

instance Attribution TypeCheck AST.StatementSequence where
   attribution TypeCheck (inherited, AST.StatementSequence statements) =
      (Synthesized SynTC{errors= foldMap (errors . syn) statements},
       AST.StatementSequence (Inherited (inh inherited) <$ statements))

instance Attribution TypeCheck AST.Statement where
   attribution TypeCheck (inherited, AST.EmptyStatement) = (Synthesized SynTC{errors= []}, AST.EmptyStatement)
   attribution TypeCheck (inherited, AST.Assignment var value) =
      (Synthesized SynTC{errors= typeCompatible (designatorType $ syn var) (inferredType $ syn value)},
       AST.Assignment (Inherited $ inh inherited) (Inherited $ inh inherited))
   attribution TypeCheck (inherited, AST.ProcedureCall procedure parameters) =
      (Synthesized SynTC{errors= case syn procedure
                                 of SynTCDes{designatorErrors= [],
                                             designatorType= ProcedureType formalTypes Nothing}
                                                   | length formalTypes /= length parameters ->
                                                       [ArgumentCountMismatch formalTypes (length parameters)]
                                                   | otherwise -> concat (zipWith typeCompatible formalTypes $
                                                                          maybe [] (inferredType . syn <$>) parameters)
                                    SynTCDes{designatorErrors= [],
                                             designatorType= t} -> [NonProcedureType t]
                                    SynTCDes{designatorErrors= errs} -> errs
                                    <> foldMap (foldMap (expressionErrors . syn)) parameters},
       AST.ProcedureCall (Inherited $ inh inherited) ((Inherited (inh inherited) <$) <$> parameters))
   attribution TypeCheck (inherited, AST.If branches fallback) =
      (Synthesized SynTC{errors= foldMap (errors . syn) branches <> foldMap (errors . syn) fallback},
       AST.If (Inherited (inh inherited) <$ branches) (Inherited (inh inherited) <$ fallback))
   attribution TypeCheck (inherited, AST.CaseStatement value branches fallback) =
      (Synthesized SynTC{errors= expressionErrors (syn value) <> foldMap (errors . syn) branches 
                                 <> foldMap (errors . syn) fallback},
       AST.CaseStatement (Inherited $ inh inherited) (Inherited (inh inherited) <$ branches)
                         (Inherited (inh inherited) <$ fallback))
   attribution TypeCheck (inherited, AST.While condition body) =
      (Synthesized SynTC{errors= booleanExpressionErrors (syn condition) <> errors (syn body)},
       AST.While (Inherited $ inh inherited) (Inherited $ inh inherited))
   attribution TypeCheck (inherited, AST.Repeat body condition) =
      (Synthesized SynTC{errors= booleanExpressionErrors (syn condition) <> errors (syn body)},
       AST.Repeat (Inherited $ inh inherited) (Inherited $ inh inherited))
   attribution TypeCheck (inherited, AST.For counter start end step body) =
      (Synthesized SynTC{errors= integerExpressionErrors (syn start) <> integerExpressionErrors (syn end) 
                                 <> foldMap (integerExpressionErrors . syn) step <> errors (syn body)},
       AST.For counter (Inherited $ inh inherited) (Inherited $ inh inherited) (Inherited (inh inherited) <$ step)
                       (Inherited $ InhTC $
                        Map.insert (AST.NonQualIdent counter) (NominalType $ AST.NonQualIdent "INTEGER")
                        $ env $ inh inherited))
   attribution TypeCheck (inherited, AST.Loop body) = (Synthesized SynTC{errors= errors (syn body)},
                                                       AST.Loop (Inherited $ inh inherited))
   attribution TypeCheck (inherited, AST.With branches fallback) =
      (Synthesized SynTC{errors= foldMap (errors . syn) branches <> foldMap (errors . syn) fallback},
       AST.With (Inherited (inh inherited) <$ branches) (Inherited (inh inherited) <$ fallback))
   attribution TypeCheck (inherited, AST.Exit) = (Synthesized SynTC{errors= []}, AST.Exit)
   attribution TypeCheck (inherited, AST.Return value) =
      (Synthesized SynTC{errors= foldMap (expressionErrors . syn) value}, 
       AST.Return (Inherited (inh inherited) <$ value))

instance Attribution TypeCheck AST.WithAlternative where
   attribution TypeCheck (inherited, AST.WithAlternative var subtype body) =
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
   attribution TypeCheck (inherited, AST.Case labels body) =
      (Synthesized SynTC{errors= foldMap (errors . syn) labels <> errors (syn body)},
       AST.Case (Inherited (inh inherited) <$ labels) (Inherited $ inh inherited))
   attribution TypeCheck (inherited, AST.EmptyCase) = (Synthesized SynTC{errors= []}, AST.EmptyCase)

instance Attribution TypeCheck AST.CaseLabels where
   attribution TypeCheck (inherited, AST.SingleLabel value) =
      (Synthesized SynTC{errors= integerExpressionErrors (syn value)},
       AST.SingleLabel (Inherited $ inh inherited))
   attribution TypeCheck (inherited, AST.LabelRange start end) =
      (Synthesized SynTC{errors= integerExpressionErrors (syn start) <> integerExpressionErrors (syn end)},
       AST.LabelRange (Inherited $ inh inherited) (Inherited $ inh inherited))

instance Attribution TypeCheck AST.Expression where
   attribution TypeCheck (inherited, AST.Relation op left right) =
      (Synthesized SynTCExp{expressionErrors= case expressionErrors (syn left) <> expressionErrors (syn right)
                                              of [] | inferredType (syn left) == inferredType (syn right) -> []
                                                    | otherwise -> [TypeMismatch
                                                                     (inferredType $ syn left)
                                                                     (inferredType $ syn right)]
                                                 errs -> errs,
                            inferredType= NominalType (AST.NonQualIdent "BOOLEAN")},
       AST.Relation op (Inherited $ inh inherited) (Inherited $ inh inherited))
   attribution TypeCheck (inherited, AST.Positive expr) =
      (Synthesized SynTCExp{expressionErrors= unaryNumericOperatorErrors (syn expr),
                            inferredType= inferredType (syn expr)},
       AST.Positive (Inherited $ inh inherited))
   attribution TypeCheck (inherited, AST.Negative expr) = 
      (Synthesized SynTCExp{expressionErrors= unaryNumericOperatorErrors (syn expr),
                            inferredType= inferredType (syn expr)},
       AST.Negative (Inherited $ inh inherited))
   attribution TypeCheck (inherited, AST.Add left right) =
      (Synthesized SynTCExp{expressionErrors= binaryNumericOperatorErrors (syn left) (syn right),
                            inferredType= inferredType (syn left)},
       AST.Add (Inherited $ inh inherited) (Inherited $ inh inherited))
   attribution TypeCheck (inherited, AST.Subtract left right) =
      (Synthesized SynTCExp{expressionErrors= binaryNumericOperatorErrors (syn left) (syn right),
                            inferredType= inferredType (syn left)},
       AST.Subtract (Inherited $ inh inherited) (Inherited $ inh inherited))
   attribution TypeCheck (inherited, AST.Or left right) =
      (Synthesized SynTCExp{expressionErrors= binaryBooleanOperatorErrors (syn left) (syn right),
                            inferredType= NominalType (AST.NonQualIdent "BOOLEAN")},
       AST.Or (Inherited $ inh inherited) (Inherited $ inh inherited))
   attribution TypeCheck (inherited, AST.Multiply left right) =
      (Synthesized SynTCExp{expressionErrors= binaryNumericOperatorErrors (syn left) (syn right),
                            inferredType= inferredType (syn left)},
       AST.Multiply (Inherited $ inh inherited) (Inherited $ inh inherited))
   attribution TypeCheck (inherited, AST.Divide left right) =
      (Synthesized SynTCExp{expressionErrors= case (syn left, syn right)
                                              of (SynTCExp{expressionErrors= [],
                                                           inferredType= NominalType (AST.NonQualIdent "REAL")},
                                                  SynTCExp{expressionErrors= [],
                                                           inferredType= NominalType (AST.NonQualIdent "REAL")}) -> []
                                                 (SynTCExp{expressionErrors= [], inferredType= t1},
                                                  SynTCExp{expressionErrors= [], inferredType= t2})
                                                   | t1 == t2 -> [UnrealType t1]
                                                   | otherwise -> [TypeMismatch t1 t2],
                            inferredType= NominalType (AST.NonQualIdent "REAL")},
       AST.Divide (Inherited $ inh inherited) (Inherited $ inh inherited))
   attribution TypeCheck (inherited, AST.IntegerDivide left right) =
      (Synthesized SynTCExp{expressionErrors= binaryIntegerOperatorErrors (syn left) (syn right),
                            inferredType= NominalType (AST.NonQualIdent "INTEGER")},
       AST.IntegerDivide (Inherited $ inh inherited) (Inherited $ inh inherited))
   attribution TypeCheck (inherited, AST.Modulo left right) =
      (Synthesized SynTCExp{expressionErrors= binaryIntegerOperatorErrors (syn left) (syn right),
                            inferredType= NominalType (AST.NonQualIdent "INTEGER")},
        AST.Modulo (Inherited $ inh inherited) (Inherited $ inh inherited))
   attribution TypeCheck (inherited, AST.And left right) =
      (Synthesized SynTCExp{expressionErrors= binaryBooleanOperatorErrors (syn left) (syn right),
                            inferredType= NominalType (AST.NonQualIdent "BOOLEAN")},
       AST.And (Inherited $ inh inherited) (Inherited $ inh inherited))
   attribution TypeCheck (inherited, AST.Integer x) =
      (Synthesized SynTCExp{expressionErrors= mempty,
                            inferredType= NominalType (AST.NonQualIdent "INTEGER")},
       AST.Integer x)
   attribution TypeCheck (inherited, AST.Real x) =
      (Synthesized SynTCExp{expressionErrors= mempty,
                            inferredType= NominalType (AST.NonQualIdent "REAL")},
       AST.Real x)
   attribution TypeCheck (inherited, AST.CharConstant x) =
      (Synthesized SynTCExp{expressionErrors= mempty,
                            inferredType= NominalType (AST.NonQualIdent "CHAR")},
       AST.CharConstant x)
   attribution TypeCheck (inherited, AST.CharCode x) =
      (Synthesized SynTCExp{expressionErrors= mempty,
                            inferredType= NominalType (AST.NonQualIdent "CHAR")},
       AST.CharCode x)
   attribution TypeCheck (inherited, AST.String x) =
      (Synthesized SynTCExp{expressionErrors= mempty,
                            inferredType= StringType (Text.length x)},
       AST.String x)
   attribution TypeCheck (inherited, AST.Nil) =
      (Synthesized SynTCExp{expressionErrors= mempty,
                            inferredType= NilType},
       AST.Nil)
   attribution TypeCheck (inherited, AST.Set elements) =
      (Synthesized SynTCExp{expressionErrors= mempty,
                            inferredType= NominalType (AST.NonQualIdent "SET")},
       AST.Set (Inherited (inh inherited) <$ elements))
   attribution TypeCheck (inherited, AST.Read designator) =
      (Synthesized SynTCExp{expressionErrors= designatorErrors (syn designator),
                            inferredType= designatorType (syn designator)},
       AST.Read (Inherited $ inh inherited))
   attribution TypeCheck (inherited, AST.FunctionCall designator parameters) =
      (Synthesized SynTCExp{expressionErrors= case syn designator
                                              of SynTCDes{designatorErrors= [],
                                                          designatorType= ProcedureType formalTypes Just{}}
                                                   | length formalTypes /= length parameters ->
                                                       [ArgumentCountMismatch formalTypes (length parameters)]
                                                   | otherwise -> concat (zipWith typeCompatible formalTypes $
                                                                          inferredType . syn <$> parameters)
                                                 SynTCDes{designatorErrors= [],
                                                          designatorType= t} -> [NonFunctionType t]
                                                 SynTCDes{designatorErrors= errs} -> errs
                                              <> foldMap (expressionErrors . syn) parameters,
                            inferredType= case syn designator
                                          of SynTCDes{designatorType= ProcedureType _ (Just returnType)} -> returnType
                                             _ -> UnknownType},
       AST.FunctionCall (Inherited $ inh inherited) (Inherited (inh inherited) <$ parameters))
   attribution TypeCheck (inherited, AST.Not expr) =
      (Synthesized SynTCExp{expressionErrors= booleanExpressionErrors (syn expr),
                            inferredType= NominalType (AST.NonQualIdent "BOOLEAN")},
       AST.Not (Inherited $ inh inherited))

instance Attribution TypeCheck AST.Element where
   attribution TypeCheck (inherited, AST.Element expr) =
      (Synthesized SynTCExp{expressionErrors= case expressionErrors (syn expr)
                                              of [] | inferredType (syn expr) 
                                                      == NominalType (AST.NonQualIdent "INTEGER") -> []
                                                    | otherwise -> [NonIntegerType (inferredType $ syn expr)]
                                                 errs -> errs,
                            inferredType= NominalType (AST.NonQualIdent "SET")},
       AST.Element (Inherited $ inh inherited))
   attribution TypeCheck (inherited, AST.Range low high) =
      (Synthesized SynTCExp{expressionErrors= case (syn low, syn high)
                                              of (SynTCExp{expressionErrors= [],
                                                           inferredType= NominalType (AST.NonQualIdent "INTEGER")},
                                                  SynTCExp{expressionErrors= [],
                                                           inferredType= NominalType (AST.NonQualIdent "INTEGER")}) 
                                                    -> []
                                                 (SynTCExp{expressionErrors= [], inferredType= t1},
                                                  SynTCExp{expressionErrors= [], inferredType= t2})
                                                    | t1 /= t2 -> [TypeMismatch t1 t2]
                                                    | otherwise -> [NonIntegerType t1]
                                                 (SynTCExp{expressionErrors= errors1}, 
                                                  SynTCExp{expressionErrors= errors2}) -> errors1 <> errors2,
                            inferredType= NominalType (AST.NonQualIdent "SET")},
       AST.Range (Inherited $ inh inherited) (Inherited $ inh inherited))

instance Attribution TypeCheck AST.Designator where
   attribution TypeCheck (inherited, AST.Variable q) =
      (Synthesized SynTCDes{designatorErrors= case designatorType
                                              of Nothing -> [UnknownName q]
                                                 Just{} -> [],
                            designatorType= fromMaybe UnknownType designatorType},
       AST.Variable q)
      where designatorType = Map.lookup q (env $ inh inherited)
   attribution TypeCheck (inherited, AST.Field record fieldName) =
      (Synthesized SynTCDes{designatorErrors= case syn record
                                              of SynTCDes{designatorErrors= [],
                                                          designatorType= RecordType _ fields}
                                                    | Map.member fieldName fields -> []
                                                    | otherwise -> [UnknownField fieldName]
                                                 SynTCDes{designatorErrors= [],
                                                          designatorType= t} -> [NonRecordType t]
                                                 SynTCDes{designatorErrors= errors} -> errors,
                            designatorType= case designatorType (syn record)
                                            of RecordType _ fields 
                                                  | Just t <- Map.lookup fieldName fields -> t
                                               _ -> UnknownType},
       AST.Field (Inherited $ inh inherited) fieldName)
   attribution TypeCheck (inherited, AST.Index array indexes) =
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
       AST.Index (Inherited $ inh inherited) (Inherited (inh inherited) <$ indexes))
   attribution TypeCheck (inherited, AST.TypeGuard designator q) =
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
   attribution TypeCheck (inherited, AST.Dereference pointer) =
      (Synthesized SynTCDes{designatorErrors= case syn pointer
                                              of SynTCDes{designatorErrors= [],
                                                          designatorType= PointerType{}} -> []
                                                 SynTCDes{designatorErrors= [],
                                                          designatorType= t} -> [NonPointerType t]
                                                 SynTCDes{designatorErrors= errors} -> errors,
                            designatorType= case designatorType (syn pointer)
                                            of PointerType t -> t
                                               _ -> UnknownType},
       AST.Dereference (Inherited $ inh inherited))

errorIfDuplicate :: Environment -> AST.Ident -> [Error]
errorIfDuplicate env name  
   | Map.member (AST.NonQualIdent name) env = [DuplicateBinding name]
   | otherwise = []

unaryNumericOperatorErrors :: SynTCExp -> [Error]
unaryNumericOperatorErrors SynTCExp{expressionErrors= [], inferredType= NominalType (AST.NonQualIdent "REAL")} = []
unaryNumericOperatorErrors SynTCExp{expressionErrors= [], inferredType= NominalType (AST.NonQualIdent "INTEGER")} = []
unaryNumericOperatorErrors SynTCExp{expressionErrors= [], inferredType= t} = [NonNumericType t]
unaryNumericOperatorErrors SynTCExp{expressionErrors= errs} = errs

binaryNumericOperatorErrors :: SynTCExp -> SynTCExp -> [Error]
binaryNumericOperatorErrors
  SynTCExp{expressionErrors= [], inferredType= NominalType (AST.NonQualIdent "REAL")}
  SynTCExp{expressionErrors= [], inferredType= NominalType (AST.NonQualIdent "REAL")} = []
binaryNumericOperatorErrors
  SynTCExp{expressionErrors= [], inferredType= NominalType (AST.NonQualIdent "INTEGER")}
  SynTCExp{expressionErrors= [], inferredType= NominalType (AST.NonQualIdent "INTEGER")} = []
binaryNumericOperatorErrors SynTCExp{expressionErrors= [], inferredType= t1}
                            SynTCExp{expressionErrors= [], inferredType= t2}
  | t1 == t2 = [NonNumericType t1]
  | otherwise = [TypeMismatch t1 t2]
binaryNumericOperatorErrors SynTCExp{expressionErrors= errs1} SynTCExp{expressionErrors= errs2} = errs1 <> errs2

binaryIntegerOperatorErrors :: SynTCExp -> SynTCExp -> [Error]
binaryIntegerOperatorErrors
  SynTCExp{expressionErrors= [], inferredType= NominalType (AST.NonQualIdent "INTEGER")}
  SynTCExp{expressionErrors= [], inferredType= NominalType (AST.NonQualIdent "INTEGER")} = []
binaryIntegerOperatorErrors SynTCExp{expressionErrors= [], inferredType= t1}
                            SynTCExp{expressionErrors= [], inferredType= t2}
  | t1 == t2 = [NonIntegerType t1]
  | otherwise = [TypeMismatch t1 t2]

integerExpressionErrors SynTCExp{expressionErrors= [],
                                 inferredType= NominalType (AST.NonQualIdent "INTEGER")} = []
integerExpressionErrors SynTCExp{expressionErrors= [], inferredType= t} = [NonIntegerType t]
integerExpressionErrors SynTCExp{expressionErrors= errs} = errs

booleanExpressionErrors SynTCExp{expressionErrors= [],
                                 inferredType= NominalType (AST.NonQualIdent "BOOLEAN")} = []
booleanExpressionErrors SynTCExp{expressionErrors= [], inferredType= t} = [NonBooleanType t]
booleanExpressionErrors SynTCExp{expressionErrors= errs} = errs

binaryBooleanOperatorErrors :: SynTCExp -> SynTCExp -> [Error]
binaryBooleanOperatorErrors
  SynTCExp{expressionErrors= [], inferredType= NominalType (AST.NonQualIdent "BOOLEAN")}
  SynTCExp{expressionErrors= [], inferredType= NominalType (AST.NonQualIdent "BOOLEAN")} = []
binaryBooleanOperatorErrors SynTCExp{expressionErrors= [], inferredType= t1}
                            SynTCExp{expressionErrors= [], inferredType= t2}
  | t1 == t2 = [NonBooleanType t1]
  | otherwise = [TypeMismatch t1 t2]

typeCompatible :: Type -> Type -> [Error]
typeCompatible expected actual
   | expected == actual = []

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
   AST.Module ident1a imports1 decls1 body1 ident1b <*> AST.Module ident2a imports2 decls2 body2 ident2b =
      AST.Module ident1a imports1 (zipWith Rank2.apply decls1 decls2) (liftA2 Rank2.apply body1 body2) ident1b

checkModules :: Environment -> Map AST.Ident (AST.Module Identity Identity) -> [Error]
checkModules predef modules = 
   errors (syn (TypeCheck Shallow.<$> Identity (TypeCheck Deep.<$> Modules (Identity <$> modules))
                `Rank2.apply`
                Inherited (InhTC predef)))

$(mconcat <$> mapM Rank2.TH.unsafeDeriveApply
  [''AST.Declaration, ''AST.Type, ''AST.Expression,
   ''AST.Element, ''AST.Designator, ''AST.FieldList,
   ''AST.ProcedureHeading, ''AST.FormalParameters, ''AST.FPSection, ''AST.ProcedureBody,
   ''AST.Statement, ''AST.StatementSequence, ''AST.WithAlternative, ''AST.Case, ''AST.CaseLabels])
