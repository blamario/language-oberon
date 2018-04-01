{-# LANGUAGE OverloadedStrings #-}

module Language.Oberon.Resolver where

import Control.Applicative (Alternative)
import Control.Monad ((>=>))
import Data.Either (partitionEithers)
import Data.Either.Validation (Validation(..), validationToEither)
import Data.Functor.Identity (Identity(..))
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.List as List
import Data.Monoid (Alt(..))
import Data.Map.Lazy (Map, traverseWithKey)
import qualified Data.Map.Lazy as Map
import Data.Semigroup (Semigroup(..), sconcat)

import Text.Grampa (Ambiguous(..))

import Language.Oberon.AST

data DeclarationRHS f = DeclaredConstant (f (ConstExpression f))
                      | DeclaredType (Type f)
                      | DeclaredVariable (Type f)
                      | DeclaredProcedure (Maybe (FormalParameters f))

data Error = UnknownModule Ident
           | UnknownLocal Ident
           | UnknownImport QualIdent
           | AmbiguousDesignator [Designator Identity]
           | AmbiguousExpression [Expression Identity]
           | AmbiguousStatement [Statement Identity]
           | InvalidDesignator (NonEmpty Error)
           | InvalidExpression (NonEmpty Error)
           | InvalidStatement (NonEmpty Error)
           | NotAProcedure QualIdent
           | NotAType QualIdent
           | NotAValue QualIdent
           | NotWriteable QualIdent
           | ClashingImports
           deriving (Show)

type Scope = Map Ident (Validation (NonEmpty Error) (DeclarationRHS Identity))

resolveModules :: Scope -> Map Ident (Module Ambiguous)
                  -> Validation (NonEmpty (Ident, NonEmpty Error)) (Map Ident (Module Identity))
resolveModules predefinedScope modules = traverseWithKey extractErrors modules'
   where modules' = resolveModule predefinedScope modules' <$> modules
         extractErrors moduleKey (Failure e)   = Failure ((moduleKey, e) :| [])
         extractErrors _         (Success mod) = Success mod

resolveModule :: Scope -> Map Ident (Validation (NonEmpty Error) (Module Identity)) -> Module Ambiguous
              -> Validation (NonEmpty Error) (Module Identity)
resolveModule predefinedScope modules (Module name imports declarations body name') = module'
   where moduleExports      :: Map Ident Scope
         moduleGlobals      :: Map Ident (AccessMode, Validation (NonEmpty Error) (DeclarationRHS Identity))
         importedModules    :: Map Ident (Validation (NonEmpty Error) (Module Identity))
         resolveBinding     :: Scope -> DeclarationRHS Ambiguous
                            -> Validation (NonEmpty Error) (DeclarationRHS Identity)
         resolveDeclaration :: Scope -> Declaration Ambiguous -> Validation (NonEmpty Error) (Declaration Identity)
         resolveType        :: Scope -> Type Ambiguous -> Validation (NonEmpty Error) (Type Identity)
         resolveFields      :: Scope -> FieldList Ambiguous -> Validation (NonEmpty Error) (FieldList Identity)
         resolveStatements  :: Scope -> StatementSequence Ambiguous
                            -> Validation (NonEmpty Error) (StatementSequence Identity)
         resolveStatement   :: Scope -> Statement Ambiguous -> Validation (NonEmpty Error) (Statement Identity)
         resolveExpression  :: Scope -> Expression Ambiguous -> Validation (NonEmpty Error) (Expression Identity)
         resolveElement     :: Scope -> Element Ambiguous -> Validation (NonEmpty Error) (Element Identity)
         resolveDesignator, resolveWriteable, resolveProcedure, resolveRecord, resolvePointer
                            :: Scope -> Designator Ambiguous -> Validation (NonEmpty Error) (Designator Identity)
         resolveName        :: Scope -> QualIdent -> Validation (NonEmpty Error) (DeclarationRHS Identity)
         resolveTypeName    :: Scope -> QualIdent -> Validation (NonEmpty Error) QualIdent

         module' = Module name imports
                   <$> traverse (resolveDeclaration moduleGlobalScope) declarations
                   <*> traverse (resolveStatements moduleGlobalScope) body
                   <*> pure name'
         importedModules = Map.delete mempty (Map.mapKeysWith clashingRenames importedAs modules)
            where importedAs moduleName = case List.find ((== moduleName) . snd) imports
                                          of Just (Nothing, moduleKey) -> moduleKey
                                             Just (Just innerKey, _) -> innerKey
                                             Nothing -> mempty
                  clashingRenames _ _ = Failure (ClashingImports :| [])

         moduleExports = foldMap exportsOfModule <$> importedModules
         moduleGlobals = (resolveBinding moduleGlobalScope <$>)
                         <$> Map.fromList (concatMap declarationBinding declarations)
         moduleGlobalScope = Map.union (snd <$> moduleGlobals) predefinedScope

         resolveDeclaration scope (ConstantDeclaration name (Ambiguous expr)) =
            ConstantDeclaration name . Identity <$> uniqueExpression (resolveExpression scope <$> expr)
         resolveDeclaration scope (TypeDeclaration name typeDef) =
            TypeDeclaration name <$> resolveType scope typeDef
         resolveDeclaration scope (VariableDeclaration name typeDef) =
            VariableDeclaration name <$> resolveType scope typeDef
         resolveDeclaration scope (ProcedureDeclaration head (ProcedureBody declarations statements) name) =
            ProcedureDeclaration <$> resolveHeading head
                                 <*> (ProcedureBody <$> sequenceA declarations'
                                                    <*> (traverse (resolveStatements scope'') statements))
                                 <*> pure name
            where scope'' = Map.union (resolveBinding scope . snd <$> Map.fromList declarationBindings) scope'
                  scope' = Map.union (headBindings head) scope
                  headBindings (ProcedureHeading receiver indirect name parameters) =
                     Map.union (foldMap receiverBinding receiver) (foldMap parametersBinding parameters)
                  receiverBinding (_, name, t) =
                     Map.singleton name (DeclaredVariable <$> resolveType scope (TypeReference $ NonQualIdent t))
                  parametersBinding (FormalParameters sections _return) = foldMap sectionBinding sections
                  sectionBinding (FPSection var names t) = foldMap parameterBinding names
                     where parameterBinding name = Map.singleton name (DeclaredVariable <$> resolveType scope t)
                     
                  declarationBindings = concatMap declarationBinding declarations
                  declarations' = resolveDeclaration scope'' <$> declarations
                  resolveHeading (ProcedureHeading receiver indirect name parameters) =
                     ProcedureHeading receiver indirect name <$> traverse (resolveParameters scope) parameters
         resolveDeclaration scope (ForwardDeclaration name parameters) =
            ForwardDeclaration name <$> traverse (resolveParameters scope) parameters

         resolveType scope (TypeReference name) = pure (TypeReference name)
         resolveType scope (ArrayType dimensions itemType) =
            ArrayType <$> (traverse (fmap Identity . uniqueExpression . (resolveExpression scope <$>) . unA) dimensions)
                      <*> resolveType scope itemType
            where unA (Ambiguous a) = a
         resolveType scope (RecordType baseType fields) = RecordType baseType <$> traverse (resolveFields scope) fields
         resolveType scope (PointerType baseType) = PointerType <$> resolveType scope baseType
         resolveType scope (ProcedureType parameters) = ProcedureType <$> traverse (resolveParameters scope) parameters

         resolveFields scope (FieldList names fieldType) = FieldList names <$> resolveType scope fieldType
         resolveFields scope EmptyFieldList = pure EmptyFieldList

         resolveParameters scope (FormalParameters sections result) =
            FormalParameters <$> traverse resolveSection sections <*> pure result
            where resolveSection (FPSection var names t) = FPSection var names <$> resolveType scope t

         resolveStatements scope = traverse (fmap Identity . resolveOne)
            where resolveOne :: Ambiguous (Statement Ambiguous) -> Validation (NonEmpty Error) (Statement Identity)
                  resolveOne (Ambiguous statements) = uniqueStatement (resolveStatement scope <$> statements)

         resolveStatement _ EmptyStatement = pure EmptyStatement
         resolveStatement scope (Assignment (Ambiguous designators) exp) =
            Assignment <$> (Identity <$> uniqueDesignator (resolveWriteable scope <$> designators))
                       <*> resolveExpression scope exp
         resolveStatement scope (ProcedureCall (Ambiguous designators) parameters) =
            ProcedureCall <$> (Identity <$> uniqueDesignator (resolveProcedure scope <$> designators))
                          <*> (traverse  . traverse) (resolveExpression scope) parameters
         resolveStatement scope (If branches fallback) =
            If <$> traverse resolveBranch branches <*> traverse (resolveStatements scope) fallback
            where resolveBranch (condition, action) = (,) <$> resolveExpression scope condition
                                                          <*> resolveStatements scope action
         resolveStatement scope (CaseStatement expression cases fallback) =
            CaseStatement <$> resolveExpression scope expression
                          <*> traverse resolveCase cases
                          <*> traverse (resolveStatements scope) fallback
            where resolveCase (Case caseLabels action) =
                     Case <$> traverse resolveLabels caseLabels <*> resolveStatements scope action
                  resolveLabels (SingleLabel expression) = SingleLabel <$> resolveExpression scope expression
                  resolveLabels (LabelRange low high) =
                     LabelRange <$> resolveExpression scope low <*> resolveExpression scope high
         resolveStatement scope (While condition body) =
            While <$> resolveExpression scope condition <*> resolveStatements scope body
         resolveStatement scope (Repeat body condition) =
            Repeat <$> resolveStatements scope body <*> resolveExpression scope condition
         resolveStatement scope (For index from to by body) =
            For index <$> resolveExpression scope from <*> resolveExpression scope to 
                      <*> traverse (resolveExpression scope) by <*> resolveStatements scope body
         resolveStatement scope (Loop body) = Loop <$> resolveStatements scope body
         resolveStatement scope (With alternatives fallback) = With <$> traverse resolveAlt alternatives
                                                                    <*> traverse (resolveStatements scope) fallback
            where resolveAlt (WithAlternative name t action) =
                     WithAlternative name t <$> resolveStatements scope action
         resolveStatement scope Exit = pure Exit
         resolveStatement scope (Return expression) = Return <$> traverse (resolveExpression scope) expression

         resolveExpression scope (Relation op left right) =
            Relation op <$> resolveExpression scope left <*> resolveExpression scope right
         resolveExpression scope (Positive e) = Positive <$> resolveExpression scope e
         resolveExpression scope (Negative e) = Negative <$> resolveExpression scope e
         resolveExpression scope (Add left right) =
            Add <$> resolveExpression scope left <*> resolveExpression scope right
         resolveExpression scope (Subtract left right) =
            Subtract <$> resolveExpression scope left <*> resolveExpression scope right
         resolveExpression scope (Or left right) =
            Or <$> resolveExpression scope left <*> resolveExpression scope right
         resolveExpression scope (Multiply left right) =
            Multiply <$> resolveExpression scope left <*> resolveExpression scope right
         resolveExpression scope (Divide left right) =
            Divide <$> resolveExpression scope left <*> resolveExpression scope right
         resolveExpression scope (IntegerDivide left right) =
            IntegerDivide <$> resolveExpression scope left <*> resolveExpression scope right
         resolveExpression scope (Modulo left right) = 
            Modulo <$> resolveExpression scope left <*> resolveExpression scope right
         resolveExpression scope (And left right) =
            And <$> resolveExpression scope left <*> resolveExpression scope right
         resolveExpression scope (Integer x) = pure (Integer x)
         resolveExpression scope (Real x) = pure (Real x)
         resolveExpression scope (CharConstant x) = pure (CharConstant x)
         resolveExpression scope (CharCode x) = pure (CharCode x)
         resolveExpression scope (String x) = pure (String x)
         resolveExpression scope Nil = pure Nil
         resolveExpression scope (Set elements) = Set <$> traverse (resolveElement scope) elements
         resolveExpression scope (Read (Ambiguous designators)) =
            Read . Identity <$> uniqueDesignator (resolveDesignator scope <$> designators)
         resolveExpression scope (FunctionCall (Ambiguous functions) parameters) =
            FunctionCall . Identity
            <$> uniqueDesignator (resolveProcedure scope <$> functions)
            <*> traverse (resolveExpression scope) parameters
         resolveExpression scope (Not e) = Negative <$> resolveExpression scope e

         resolveElement scope (Element e) = Element <$> resolveExpression scope e
         resolveElement scope (Range left right) =
            Range <$> resolveExpression scope left <*> resolveExpression scope right

         resolveDesignator scope (Variable q) =
            case resolveName scope q
            of Failure err ->  Failure err
               Success DeclaredType{} -> Failure (NotAValue q :| [])
               Success _ -> Success (Variable q)
         resolveDesignator scope (Field record field) = Field <$> resolveRecord scope record <*> pure field
         resolveDesignator scope (Index array indexes) = Index <$> resolveArray scope array
                                                               <*> traverse (resolveExpression scope) indexes
         resolveDesignator scope (TypeGuard designator subtype) = TypeGuard <$> resolveDesignator scope designator
                                                                  <*> resolveTypeName scope subtype
         resolveDesignator scope (Dereference pointer) = Dereference <$> resolvePointer scope pointer

         resolveTypeName scope q =
            case resolveName scope q
            of Failure err ->  Failure err
               Success DeclaredType{} -> Success q
               Success _ -> Failure (NotAType q :| [])

         resolveProcedure scope d@(Variable q) =
            case resolveName scope q
            of Failure err ->  Failure err
               Success DeclaredType{} -> Failure (NotAValue q :| [])
               Success DeclaredProcedure{} -> resolveDesignator scope d
               Success _ -> resolveDesignator scope d
         resolveProcedure scope d = resolveDesignator scope d

         resolveWriteable scope d@(Variable q) =
            case resolveName scope q
            of Failure err ->  Failure err
               Success DeclaredType{} -> Failure (NotAValue q :| [])
               Success DeclaredProcedure{} -> Failure (NotWriteable q :| [])
               Success DeclaredConstant{} -> Failure (NotWriteable q :| [])
               Success DeclaredVariable{} -> resolveDesignator scope d
         resolveWriteable scope d = resolveDesignator scope d

         resolveRecord = resolveDesignator
         resolveArray = resolveDesignator
         resolvePointer = resolveDesignator

         resolveName scope q@(QualIdent moduleName name) =
            case Map.lookup moduleName moduleExports
            of Nothing -> Failure (UnknownModule moduleName :| [])
               Just exports -> case Map.lookup name exports
                               of Just (Success rhs) -> Success rhs
                                  Nothing -> Failure (UnknownImport q :| [])
         resolveName scope (NonQualIdent name) =
            case Map.lookup name scope
            of Just (Success rhs) -> Success rhs
               _ -> Failure (UnknownLocal name :| [])
               

         resolveBinding scope (DeclaredConstant (Ambiguous expression)) =
            DeclaredConstant . Identity <$> uniqueExpression (resolveExpression scope <$> expression)
         resolveBinding scope (DeclaredType typeDef) = DeclaredType <$> resolveType scope typeDef
         resolveBinding scope (DeclaredVariable typeDef) = DeclaredVariable <$> resolveType scope typeDef
         resolveBinding scope (DeclaredProcedure parameters) =
            DeclaredProcedure <$> traverse (resolveParameters scope) parameters
         
declarationBinding :: Declaration f -> [(Ident, (AccessMode, DeclarationRHS f))]
declarationBinding (ConstantDeclaration (IdentDef name export) expr) =
   [(name, (export, DeclaredConstant expr))]
declarationBinding (TypeDeclaration (IdentDef name export) typeDef) =
   [(name, (export, DeclaredType typeDef))]
declarationBinding (VariableDeclaration names typeDef) =
   [(name, (export, DeclaredVariable typeDef)) | (IdentDef name export) <- NonEmpty.toList names]
declarationBinding (ProcedureDeclaration (ProcedureHeading _ _ (IdentDef name export) parameters) _ _) =
   [(name, (export, DeclaredProcedure parameters))]
declarationBinding (ForwardDeclaration (IdentDef name export) parameters) =
   [(name, (export, DeclaredProcedure parameters))]

predefined, predefined2 :: Scope
predefined = Success <$> Map.fromList
   [("BOOLEAN", DeclaredType (TypeReference $ NonQualIdent "BOOLEAN")),
    ("CHAR", DeclaredType (TypeReference $ NonQualIdent "CHAR")),
    ("SHORTINT", DeclaredType (TypeReference $ NonQualIdent "SHORTINT")),
    ("INTEGER", DeclaredType (TypeReference $ NonQualIdent "INTEGER")),
    ("LONGINT", DeclaredType (TypeReference $ NonQualIdent "LONGINT")),
    ("REAL", DeclaredType (TypeReference $ NonQualIdent "REAL")),
    ("LONGREAL", DeclaredType (TypeReference $ NonQualIdent "LONGREAL")),
    ("SET", DeclaredType (TypeReference $ NonQualIdent "SET")),
    ("TRUE", DeclaredConstant (Identity $ Read $ Identity $ Variable $ NonQualIdent "TRUE")),
    ("FALSE", DeclaredConstant (Identity $ Read $ Identity $ Variable $ NonQualIdent "FALSE")),
    ("ABS", DeclaredProcedure $ Just $
            FormalParameters [FPSection False (pure "n") $ TypeReference $ NonQualIdent "INTEGER"] $
            Just $ NonQualIdent "INTEGER"),
    ("ASH", DeclaredProcedure $ Just $
            FormalParameters [FPSection False (pure "n") $ TypeReference $ NonQualIdent "INTEGER"] $
            Just $ NonQualIdent "INTEGER"),
    ("CAP", DeclaredProcedure $ Just $
            FormalParameters [FPSection False (pure "c") $ TypeReference $ NonQualIdent "INTEGER"] $
            Just $ NonQualIdent "CAP"),
    ("LEN", DeclaredProcedure $ Just $
            FormalParameters [FPSection False (pure "c") $ TypeReference $ NonQualIdent "ARRAY"] $
            Just $ NonQualIdent "LONGINT"),
    ("MAX", DeclaredProcedure $ Just $
            FormalParameters [FPSection False (pure "c") $ TypeReference $ NonQualIdent "SET"] $
            Just $ NonQualIdent "INTEGER"),
    ("MIN", DeclaredProcedure $ Just $
            FormalParameters [FPSection False (pure "c") $ TypeReference $ NonQualIdent "SET"] $
            Just $ NonQualIdent "INTEGER"),
    ("ODD", DeclaredProcedure $ Just $
            FormalParameters [FPSection False (pure "n") $ TypeReference $ NonQualIdent "CHAR"] $
            Just $ NonQualIdent "BOOLEAN"),
    ("SIZE", DeclaredProcedure $ Just $
             FormalParameters [FPSection False (pure "n") $ TypeReference $ NonQualIdent "CHAR"] $
             Just $ NonQualIdent "INTEGER"),
    ("ORD", DeclaredProcedure $ Just $
            FormalParameters [FPSection False (pure "n") $ TypeReference $ NonQualIdent "CHAR"] $
            Just $ NonQualIdent "INTEGER"),
    ("CHR", DeclaredProcedure $ Just $
            FormalParameters [FPSection False (pure "n") $ TypeReference $ NonQualIdent "INTEGER"] $
            Just $ NonQualIdent "CHAR"),
    ("SHORT", DeclaredProcedure $ Just $
              FormalParameters [FPSection False (pure "n") $ TypeReference $ NonQualIdent "INTEGER"] $
              Just $ NonQualIdent "INTEGER"),
    ("LONG", DeclaredProcedure $ Just $
             FormalParameters [FPSection False (pure "n") $ TypeReference $ NonQualIdent "INTEGER"] $
             Just $ NonQualIdent "INTEGER"),
    ("ENTIER", DeclaredProcedure $ Just $
               FormalParameters [FPSection False (pure "n") $ TypeReference $ NonQualIdent "REAL"] $
               Just $ NonQualIdent "INTEGER"),
    ("INC", DeclaredProcedure $ Just $
            FormalParameters [FPSection False (pure "n") $ TypeReference $ NonQualIdent "INTEGER"] Nothing),
    ("DEC", DeclaredProcedure $ Just $
            FormalParameters [FPSection False (pure "n") $ TypeReference $ NonQualIdent "INTEGER"] Nothing),
    ("INCL", DeclaredProcedure $ Just $
             FormalParameters [FPSection False (pure "s") $ TypeReference $ NonQualIdent "SET",
                               FPSection False (pure "n") $ TypeReference $ NonQualIdent "INTEGER"] Nothing),
    ("EXCL", DeclaredProcedure $ Just $
             FormalParameters [FPSection False (pure "s") $ TypeReference $ NonQualIdent "SET",
                               FPSection False (pure "n") $ TypeReference $ NonQualIdent "INTEGER"] Nothing),
    ("COPY", DeclaredProcedure $ Just $
             FormalParameters [FPSection False (pure "s") $ TypeReference $ NonQualIdent "ARRAY",
                               FPSection False (pure "n") $ TypeReference $ NonQualIdent "ARRAY"] Nothing),
    ("NEW", DeclaredProcedure $ Just $
            FormalParameters [FPSection False (pure "n") $ TypeReference $ NonQualIdent "POINTER"] Nothing),
    ("HALT", DeclaredProcedure $ Just $
             FormalParameters [FPSection False (pure "n") $ TypeReference $ NonQualIdent "INTEGER"] Nothing)]

predefined2 = predefined <>
   (Success <$> Map.fromList
    [("ASSERT", DeclaredProcedure $ Just $
             FormalParameters [FPSection False (pure "s") $ TypeReference $ NonQualIdent "ARRAY",
                               FPSection False (pure "n") $ TypeReference $ NonQualIdent "ARRAY"] Nothing)])

exportsOfModule :: Module Identity -> Scope
exportsOfModule = Map.mapMaybe isExported . globalsOfModule
   where isExported (PrivateOnly, _) = Nothing
         isExported (_, binding) = Just binding

globalsOfModule :: Module Identity -> Map Ident (AccessMode, Validation (NonEmpty Error) (DeclarationRHS Identity))
globalsOfModule (Module _ imports declarations _ _) = scope'
   where scope' = (Success <$>) <$> Map.fromList declarationBindings
         declarationBindings = concatMap declarationBinding declarations

uniqueDesignator = unique InvalidDesignator AmbiguousDesignator
uniqueExpression = unique InvalidExpression AmbiguousExpression
uniqueStatement = unique InvalidStatement AmbiguousStatement

unique :: (NonEmpty Error -> Error) -> ([a] -> Error) 
          -> NonEmpty (Validation (NonEmpty Error) a) -> Validation (NonEmpty Error) a
unique _ _ (x :| []) = x
unique inv amb xs = case partitionEithers (validationToEither <$> NonEmpty.toList xs)
                     of (_, [x]) -> Success x
                        (errors, []) -> Failure (inv (sconcat $ NonEmpty.fromList errors) :| [])
                        (_, stats) -> Failure (amb stats :| [])
