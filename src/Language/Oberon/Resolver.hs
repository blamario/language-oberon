{-# LANGUAGE OverloadedStrings #-}

module Language.Oberon.Resolver where

import Control.Applicative (Alternative)
import Control.Monad ((>=>))
import Data.Either (partitionEithers)
import Data.Either.Validation (Validation(..), validationToEither)
import Data.Functor.Identity (Identity(..))
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty
import Data.Monoid (Alt(..))
import Data.Map.Lazy (Map, traverseWithKey)
import qualified Data.Map.Lazy as Map
import Data.Semigroup (Semigroup(..), sconcat)

import Text.Grampa (Ambiguous(..))

import Language.Oberon.AST

data DeclarationRHS = DeclaredConstant (ConstExpression Identity)
                    | DeclaredType (Type Identity)
                    | DeclaredVariable (Type Identity)
                    | DeclaredProcedure (Maybe FormalParameters)
   
data Error = UnknownModule Ident
           | UnknownLocal Ident
           | UnknownImport QualIdent
           | AmbiguousStatement [Statement Identity]
           | InvalidStatement (NonEmpty Error)
           | AmbiguousDesignator [Designator Identity]
           | InvalidDesignator (NonEmpty Error)
           | NotAProcedure QualIdent
           | NotAType QualIdent
           | NotAValue QualIdent
           | NotWriteable QualIdent

resolveModules :: Map Ident (Module Ambiguous) 
                       -> Validation (NonEmpty (Ident, NonEmpty Error)) (Map Ident (Module Identity))
resolveModules modules = traverseWithKey extractErrors modules'
   where modules' = resolveModule modules' <$> modules
         extractErrors moduleKey (Failure e)   = Failure ((moduleKey, e) :| [])
         extractErrors _         (Success mod) = Success mod

resolveModule :: Map Ident (Validation (NonEmpty Error) (Module Identity)) -> Module Ambiguous
              -> Validation (NonEmpty Error) (Module Identity)
resolveModule modules (Module name imports declarations body name') = module'
   where moduleExports      :: Map Ident (Map Ident DeclarationRHS)
         moduleGlobals      :: Map Ident (Bool, DeclarationRHS)
         resolveDeclaration :: Map Ident DeclarationRHS -> Declaration Ambiguous
                            -> Validation (NonEmpty Error) (Declaration Identity)
         resolveType        :: Map Ident DeclarationRHS -> Type Ambiguous
                            -> Validation (NonEmpty Error) (Type Identity)
         resolveFields      :: Map Ident DeclarationRHS -> FieldList Ambiguous
                            -> Validation (NonEmpty Error) (FieldList Identity)
         resolveStatements  :: Map Ident DeclarationRHS -> StatementSequence Ambiguous
                            -> Validation (NonEmpty Error) (StatementSequence Identity)
         resolveStatement   :: Map Ident DeclarationRHS -> Statement Ambiguous
                            -> Validation (NonEmpty Error) (Statement Identity)
         resolveExpression  :: Map Ident DeclarationRHS -> Expression Ambiguous
                            -> Validation (NonEmpty Error) (Expression Identity)
         resolveElement     :: Map Ident DeclarationRHS -> Element Ambiguous
                            -> Validation (NonEmpty Error) (Element Identity)
         resolveDesignator, resolveWriteable, resolveProcedure, resolveRecord, resolvePointer
                            :: Map Ident DeclarationRHS -> Designator Ambiguous
                            -> Validation (NonEmpty Error) (Designator Identity)
         resolveName        :: Map Ident DeclarationRHS -> QualIdent
                            -> Validation (NonEmpty Error) DeclarationRHS
         resolveTypeName    :: Map Ident DeclarationRHS -> QualIdent
                            -> Validation (NonEmpty Error) QualIdent

         module' = Module name imports 
                   <$> traverse (resolveDeclaration moduleGlobalScope) declarations 
                   <*> traverse (resolveStatements moduleGlobalScope) body 
                   <*> pure name'

         moduleExports = foldMap exportsOfModule <$> modules
         moduleGlobals = foldMap globalsOfModule module'
         moduleGlobalScope = Map.union (snd <$> moduleGlobals) predefined

         resolveDeclaration scope (ConstantDeclaration name expr) =
            ConstantDeclaration name <$> resolveExpression scope expr
         resolveDeclaration scope (TypeDeclaration name typeDef) =
            TypeDeclaration name <$> resolveType scope typeDef
         resolveDeclaration scope (VariableDeclaration name typeDef) =
            VariableDeclaration name <$> resolveType scope typeDef
         resolveDeclaration scope (ProcedureDeclaration head (ProcedureBody declarations statements) name) =
            ProcedureDeclaration head <$> (ProcedureBody <$> sequenceA declarations'
                                                         <*> (traverse (resolveStatements scope') statements))
                                      <*> pure name
            where scope' = Map.union (snd <$> foldMap (either mempty declarationBinding . validationToEither) declarations') scope
                  declarations' = resolveDeclaration scope' <$> declarations
         resolveDeclaration scope (ForwardDeclaration name parameters) = pure (ForwardDeclaration name parameters)

         resolveType scope (TypeReference name) = pure (TypeReference name)
         resolveType scope (ArrayType dimensions itemType) =
            ArrayType <$> (traverse (resolveExpression scope) dimensions) <*> resolveType scope itemType
         resolveType scope (RecordType baseType fields) = RecordType baseType <$> traverse (resolveFields scope) fields
         resolveType scope (PointerType baseType) = PointerType <$> resolveType scope baseType
         resolveType scope (ProcedureType parameters) = pure (ProcedureType parameters)

         resolveFields scope (FieldList names fieldType) = FieldList names <$> resolveType scope fieldType

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
         resolveStatement scope (With inner outer body) = With inner outer <$> resolveStatements scope body
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

         resolveDesignator scope (Variable q@(QualIdent moduleName name)) =
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

         resolveWriteable scope d@(Variable q) =
            case resolveName scope q
            of Failure err ->  Failure err
               Success DeclaredType{} -> Failure (NotAValue q :| [])
               Success DeclaredProcedure{} -> Failure (NotWriteable q :| [])
               Success DeclaredConstant{} -> Failure (NotWriteable q :| [])
               Success DeclaredVariable{} -> resolveDesignator scope d

         resolveRecord = resolveDesignator
         resolveArray = resolveDesignator
         resolvePointer = resolveDesignator

         resolveName scope q@(QualIdent moduleName name) =
            case Map.lookup moduleName moduleExports
            of Nothing -> Failure (UnknownModule moduleName :| [])
               Just exports -> case Map.lookup name exports
                               of Nothing -> Failure (UnknownImport q :| [])
                                  Just rhs -> Success rhs
         resolveName scope (NonQualIdent name) =
            case Map.lookup name scope
            of Nothing -> Failure (UnknownLocal name :| [])
               Just rhs -> Success rhs

declarationBinding (ConstantDeclaration (IdentDef name export) expr) =
   Map.singleton name (export, DeclaredConstant expr)
declarationBinding (TypeDeclaration (IdentDef name export) typeDef) =
   Map.singleton name (export, DeclaredType typeDef)
declarationBinding (VariableDeclaration names typeDef) =
   foldMap (\(IdentDef name export)-> Map.singleton name (export, DeclaredVariable typeDef)) names
declarationBinding (ProcedureDeclaration (ProcedureHeading _ (IdentDef name export) parameters) _ _) =
   Map.singleton name (export, DeclaredProcedure parameters)
declarationBinding (ForwardDeclaration (IdentDef name export) parameters) =
   Map.singleton name (export, DeclaredProcedure parameters)

predefined :: Map Ident DeclarationRHS
predefined = Map.fromList
   [("BOOLEAN", DeclaredType (TypeReference $ NonQualIdent "BOOLEAN")),
    ("CHAR", DeclaredType (TypeReference $ NonQualIdent "CHAR")),
    ("SHORTINT", DeclaredType (TypeReference $ NonQualIdent "SHORTINT")),
    ("INTEGER", DeclaredType (TypeReference $ NonQualIdent "INTEGER")),
    ("LONGINT", DeclaredType (TypeReference $ NonQualIdent "LONGINT")),
    ("REAL", DeclaredType (TypeReference $ NonQualIdent "REAL")),
    ("LONGREAL", DeclaredType (TypeReference $ NonQualIdent "LONGREAL")),
    ("SET", DeclaredType (TypeReference $ NonQualIdent "SET")),
    ("TRUE", DeclaredConstant (Read $ Identity $ Variable $ NonQualIdent "TRUE")),
    ("FALSE", DeclaredConstant (Read $ Identity $ Variable $ NonQualIdent "FALSE")),
    ("ABS", DeclaredProcedure $ Just $
            FormalParameters [FPSection False (pure "n") $ FormalTypeReference $ NonQualIdent "INTEGER"] $
            Just $ NonQualIdent "INTEGER"),
    ("ASH", DeclaredProcedure $ Just $
            FormalParameters [FPSection False (pure "n") $ FormalTypeReference $ NonQualIdent "INTEGER"] $
            Just $ NonQualIdent "INTEGER"),
    ("CAP", DeclaredProcedure $ Just $
            FormalParameters [FPSection False (pure "c") $ FormalTypeReference $ NonQualIdent "INTEGER"] $
            Just $ NonQualIdent "CAP"),
    ("LEN", DeclaredProcedure $ Just $
            FormalParameters [FPSection False (pure "c") $ FormalTypeReference $ NonQualIdent "ARRAY"] $
            Just $ NonQualIdent "LONGINT"),
    ("MAX", DeclaredProcedure $ Just $
            FormalParameters [FPSection False (pure "c") $ FormalTypeReference $ NonQualIdent "SET"] $
            Just $ NonQualIdent "INTEGER"),
    ("MIN", DeclaredProcedure $ Just $
            FormalParameters [FPSection False (pure "c") $ FormalTypeReference $ NonQualIdent "SET"] $
            Just $ NonQualIdent "INTEGER"),
    ("ODD", DeclaredProcedure $ Just $
            FormalParameters [FPSection False (pure "n") $ FormalTypeReference $ NonQualIdent "CHAR"] $
            Just $ NonQualIdent "BOOLEAN"),
    ("SIZE", DeclaredProcedure $ Just $
             FormalParameters [FPSection False (pure "n") $ FormalTypeReference $ NonQualIdent "CHAR"] $
             Just $ NonQualIdent "INTEGER"),
    ("ORD", DeclaredProcedure $ Just $
            FormalParameters [FPSection False (pure "n") $ FormalTypeReference $ NonQualIdent "CHAR"] $
            Just $ NonQualIdent "INTEGER"),
    ("CHR", DeclaredProcedure $ Just $
            FormalParameters [FPSection False (pure "n") $ FormalTypeReference $ NonQualIdent "INTEGER"] $
            Just $ NonQualIdent "CHAR"),
    ("SHORT", DeclaredProcedure $ Just $
              FormalParameters [FPSection False (pure "n") $ FormalTypeReference $ NonQualIdent "INTEGER"] $
              Just $ NonQualIdent "INTEGER"),
    ("LONG", DeclaredProcedure $ Just $
             FormalParameters [FPSection False (pure "n") $ FormalTypeReference $ NonQualIdent "INTEGER"] $
             Just $ NonQualIdent "INTEGER"),
    ("ENTIER", DeclaredProcedure $ Just $
               FormalParameters [FPSection False (pure "n") $ FormalTypeReference $ NonQualIdent "REAL"] $
               Just $ NonQualIdent "INTEGER"),
    ("INC", DeclaredProcedure $ Just $
            FormalParameters [FPSection False (pure "n") $ FormalTypeReference $ NonQualIdent "INTEGER"] Nothing),
    ("DEC", DeclaredProcedure $ Just $
            FormalParameters [FPSection False (pure "n") $ FormalTypeReference $ NonQualIdent "INTEGER"] Nothing),
    ("INCL", DeclaredProcedure $ Just $
             FormalParameters [FPSection False (pure "s") $ FormalTypeReference $ NonQualIdent "SET",
                               FPSection False (pure "n") $ FormalTypeReference $ NonQualIdent "INTEGER"] Nothing),
    ("EXCL", DeclaredProcedure $ Just $
             FormalParameters [FPSection False (pure "s") $ FormalTypeReference $ NonQualIdent "SET",
                               FPSection False (pure "n") $ FormalTypeReference $ NonQualIdent "INTEGER"] Nothing),
    ("COPY", DeclaredProcedure $ Just $
             FormalParameters [FPSection False (pure "s") $ FormalTypeReference $ NonQualIdent "ARRAY",
                               FPSection False (pure "n") $ FormalTypeReference $ NonQualIdent "ARRAY"] Nothing),
    ("NEW", DeclaredProcedure $ Just $
            FormalParameters [FPSection False (pure "n") $ FormalTypeReference $ NonQualIdent "POINTER"] Nothing),
    ("HALT", DeclaredProcedure $ Just $
             FormalParameters [FPSection False (pure "n") $ FormalTypeReference $ NonQualIdent "INTEGER"] Nothing)]

exportsOfModule :: Module Identity -> Map Ident DeclarationRHS
exportsOfModule = Map.mapMaybe isExported . globalsOfModule
   where isExported (True, binding) = Just binding
         isExported (False, _) = Nothing

globalsOfModule :: Module Identity -> Map Ident (Bool, DeclarationRHS)
globalsOfModule (Module _ imports declarations _ _) = foldMap declarationBinding declarations

uniqueDesignator = unique InvalidDesignator AmbiguousDesignator
uniqueStatement = unique InvalidStatement AmbiguousStatement

unique :: (NonEmpty Error -> Error) -> ([a] -> Error) 
          -> NonEmpty (Validation (NonEmpty Error) a) -> Validation (NonEmpty Error) a
unique _ _ (x :| []) = x
unique inv amb xs = case partitionEithers (validationToEither <$> NonEmpty.toList xs)
                     of (_, [x]) -> Success x
                        (errors, []) -> Failure (inv (sconcat $ NonEmpty.fromList errors) :| [])
                        (_, stats) -> Failure (amb stats :| [])
