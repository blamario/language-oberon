{-# LANGUAGE FlexibleInstances, OverloadedStrings, StandaloneDeriving #-}

-- | This module exports functions for resolving the syntactic ambiguities in a parsed module. For example, an Oberon
-- expression @foo(bar)@ may be a call to function @foo@ with a parameter @bar@, or it may be type guard on variable
-- @foo@ casting it to type @bar@.

module Language.Oberon.Resolver (Error(..),
                                 Predefined, predefined, predefined2, resolveModule, resolveModules) where

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

import qualified Rank2.Attributes as Rank2A (Product(Pair))
import Text.Grampa (Ambiguous(..), ParseFailure)

import Language.Oberon.AST

data DeclarationRHS f = DeclaredConstant (f (ConstExpression f f))
                      | DeclaredType (f (Type f f))
                      | DeclaredVariable (f (Type f f))
                      | DeclaredProcedure Bool (Maybe (f (FormalParameters f f)))
deriving instance Show (DeclarationRHS Identity)
deriving instance Show (DeclarationRHS Ambiguous)

-- | All possible resultion errors
data Error = UnknownModule Ident
           | UnknownLocal Ident
           | UnknownImport QualIdent
           | AmbiguousParses
           | AmbiguousBinding [(Ident, (AccessMode, DeclarationRHS Ambiguous))]
           | AmbiguousBranch [Rank2A.Product Expression StatementSequence Identity Identity]
           | AmbiguousCase [Case Identity Identity]
           | AmbiguousDeclaration [Declaration Identity Identity]
           | AmbiguousDesignator [Designator Identity Identity]
           | AmbiguousExpression [Expression Identity Identity]
           | AmbiguousElement [Element Identity Identity]
           | AmbiguousFields [FieldList Identity Identity]
           | AmbiguousLabels [CaseLabels Identity Identity]
           | AmbiguousParameters [FormalParameters Identity Identity]
           | AmbiguousSection [FPSection Identity Identity]
           | AmbiguousStatement [Statement Identity Identity]
           | AmbiguousStatements [StatementSequence Identity Identity]
           | AmbiguousType [Type Identity Identity]
           | AmbiguousWithAlternative [WithAlternative Identity Identity]
           | InvalidDeclaration (NonEmpty Error)
           | InvalidDesignator (NonEmpty Error)
           | InvalidExpression (NonEmpty Error)
           | InvalidStatement (NonEmpty Error)
           | NotAProcedure QualIdent
           | NotARecord QualIdent
           | NotAType QualIdent
           | NotATypeDesignator (Designator Ambiguous Ambiguous)
           | NotAValue QualIdent
           | NotWriteable QualIdent
           | ClashingImports
           | UnparseableModule ParseFailure
           deriving (Show)

type Scope = Predefined

-- | A set of 'Predefined' declarations.
type Predefined = Map Ident (Validation (NonEmpty Error) (DeclarationRHS Identity))

-- | Eliminate the ambiguites in the given map of module names to their parsed syntax trees. The first argument is a set
-- of 'Predefined' declarations, such as 'predefined' or 'predefined2'.
resolveModules :: Predefined -> Map Ident (Module Ambiguous Ambiguous)
               -> Validation (NonEmpty (Ident, NonEmpty Error)) (Map Ident (Module Identity Identity))
resolveModules predefinedScope modules = traverseWithKey extractErrors modules'
   where modules' = resolveModule predefinedScope modules' <$> modules
         extractErrors moduleKey (Failure e)   = Failure ((moduleKey, e) :| [])
         extractErrors _         (Success mod) = Success mod

-- | Eliminate the ambiguites in the parsed syntax tree of a single module. The first argument is a set of 'Predefined'
-- declarations, such as 'predefined' or 'predefined2'. The second is a mapping of imported module names to their
-- already resolved syntax trees.
resolveModule :: Predefined -> Map Ident (Validation (NonEmpty Error) (Module Identity Identity)) 
              -> Module Ambiguous Ambiguous
              -> Validation (NonEmpty Error) (Module Identity Identity)
resolveModule predefinedScope modules (Module moduleName imports declarations body name') = module'
   where moduleExports      :: Map Ident Scope
         moduleGlobals      :: Map Ident (AccessMode, Validation (NonEmpty Error) (DeclarationRHS Identity))
         importedModules    :: Map Ident (Validation (NonEmpty Error) (Module Identity Identity))
         resolveBinding     :: Scope -> DeclarationRHS Ambiguous
                            -> Validation (NonEmpty Error) (DeclarationRHS Identity)
         resolveDeclaration :: Scope -> Declaration Ambiguous Ambiguous 
                            -> Validation (NonEmpty Error) (Declaration Identity Identity)
         resolveType        :: Scope -> Type Ambiguous Ambiguous
                            -> Validation (NonEmpty Error) (Type Identity Identity)
         resolveFields      :: Scope -> FieldList Ambiguous Ambiguous 
                            -> Validation (NonEmpty Error) (FieldList Identity Identity)
         resolveStatements  :: Scope -> StatementSequence Ambiguous Ambiguous
                            -> Validation (NonEmpty Error) (StatementSequence Identity Identity)
         resolveStatement   :: Scope -> Statement Ambiguous Ambiguous 
                            -> Validation (NonEmpty Error) (Statement Identity Identity)
         resolveExpression  :: Scope -> Expression Ambiguous Ambiguous 
                            -> Validation (NonEmpty Error) (Expression Identity Identity)
         resolveElement     :: Scope -> Element Ambiguous Ambiguous -> Validation (NonEmpty Error) (Element Identity Identity)
         resolveDesignator, resolveWriteable, resolveProcedure, resolveRecord, resolvePointer
                            :: Scope -> Designator Ambiguous Ambiguous
                            -> Validation (NonEmpty Error) (Designator Identity Identity)
         resolveName        :: Scope -> QualIdent -> Validation (NonEmpty Error) (DeclarationRHS Identity)
         resolveTypeName    :: Scope -> QualIdent -> Validation (NonEmpty Error) QualIdent

         module' = Module moduleName imports
                   <$> traverse (uniqueDeclaration . (resolveDeclaration moduleGlobalScope <$>)) declarations
                   <*> traverse (uniqueStatements . (resolveStatements moduleGlobalScope <$>)) body
                   <*> pure name'
         importedModules = Map.delete mempty (Map.mapKeysWith clashingRenames importedAs modules)
            where importedAs moduleName = case List.find ((== moduleName) . snd) imports
                                          of Just (Nothing, moduleKey) -> moduleKey
                                             Just (Just innerKey, _) -> innerKey
                                             Nothing -> mempty
                  clashingRenames _ _ = Failure (ClashingImports :| [])

         moduleExports = foldMap exportsOfModule <$> importedModules
         moduleGlobals = (resolveBinding moduleGlobalScope <$>)
                         <$> Map.fromList (concatMap (declarationBinding moduleName . unamb) declarations)
         moduleGlobalScope = Map.union (snd <$> moduleGlobals) predefinedScope
         unamb (Ambiguous (x :| [])) = x

         resolveDeclaration scope (ConstantDeclaration name expr) =
            ConstantDeclaration name <$> uniqueExpression (resolveExpression scope <$> expr)
         resolveDeclaration scope (TypeDeclaration name typeDef) =
            TypeDeclaration name <$> uniqueType (resolveType scope <$> typeDef)
         resolveDeclaration scope (VariableDeclaration name typeDef) =
            VariableDeclaration name <$> uniqueType (resolveType scope <$> typeDef)
         resolveDeclaration scope (ProcedureDeclaration head (ProcedureBody declarations statements) name) =
            ProcedureDeclaration <$> resolveHeading head
                                 <*> (ProcedureBody <$> sequenceA (declarations')
                                                    <*> (traverse (uniqueStatements . (resolveStatements scope'' <$>))
                                                                  statements))
                                 <*> pure name
            where scope'' = Map.union (resolveBinding scope . snd <$> Map.fromList declarationBindings) scope'
                  scope' = Map.union (headBindings head) scope
                  headBindings (ProcedureHeading receiver indirect name parameters) =
                     Map.union (foldMap receiverBinding receiver) (foldMap (foldMap parametersBinding) parameters)
                  receiverBinding (_, name, t) =
                     Map.singleton name (DeclaredVariable . Identity
                                         <$> resolveType scope (TypeReference $ NonQualIdent t))
                  parametersBinding (FormalParameters sections _return) =
                     foldMap (sectionBinding . (\(Ambiguous (s :| []))-> s)) sections
                  sectionBinding (FPSection var names t) = foldMap parameterBinding names
                     where parameterBinding name =
                              Map.singleton name (DeclaredVariable <$> uniqueType (resolveType scope <$> t))
                     
                  declarationBindings = concatMap (declarationBinding moduleName . unamb) declarations
                  declarations' = uniqueDeclaration . (resolveDeclaration scope'' <$>) <$> declarations
                  resolveHeading (ProcedureHeading receiver indirect name parameters) =
                     ProcedureHeading receiver indirect name
                     <$> traverse (uniqueParameters . (resolveParameters scope <$>)) parameters
         resolveDeclaration scope (ForwardDeclaration name parameters) =
            ForwardDeclaration name <$> traverse (uniqueParameters . (resolveParameters scope <$>)) parameters

         resolveType scope (TypeReference name) = pure (TypeReference name)
         resolveType scope (ArrayType dimensions itemType) =
            ArrayType <$> (traverse (uniqueExpression . (resolveExpression scope <$>)) dimensions)
                      <*> uniqueType (resolveType scope <$> itemType)
         resolveType scope (RecordType baseType fields) =
            RecordType baseType <$> traverse (uniqueFields . (resolveFields scope <$>)) fields
         resolveType scope (PointerType baseType) = PointerType <$> uniqueType (resolveType scope <$> baseType)
         resolveType scope (ProcedureType parameters) =
            ProcedureType <$> traverse (uniqueParameters . (resolveParameters scope <$>)) parameters

         resolveFields scope (FieldList names fieldType) =
            FieldList names <$> uniqueType (resolveType scope <$> fieldType)
         resolveFields scope EmptyFieldList = pure EmptyFieldList

         resolveParameters scope (FormalParameters sections result) =
            FormalParameters <$> traverse (uniqueSection . fmap resolveSection) sections <*> pure result
            where resolveSection (FPSection var names t) = FPSection var names <$> uniqueType (resolveType scope <$> t)

         resolveStatements scope (StatementSequence statements) = StatementSequence <$> traverse resolveOne statements
            where resolveOne :: Ambiguous (Statement Ambiguous Ambiguous)
                             -> Validation (NonEmpty Error) (Identity (Statement Identity Identity))
                  resolveOne statements = uniqueStatement (resolveStatement scope <$> statements)

         resolveStatement _ EmptyStatement = pure EmptyStatement
         resolveStatement scope (Assignment designator exp) =
            Assignment <$> (uniqueDesignator (resolveWriteable scope <$> designator))
                       <*> uniqueExpression (resolveExpression scope <$> exp)
         resolveStatement scope (ProcedureCall designators parameters) =
            ProcedureCall <$> (uniqueDesignator (resolveProcedure scope <$> designators))
                          <*> traverse (traverse (uniqueExpression . (resolveExpressionOrType scope <$>))) parameters
         resolveStatement scope (If branches fallback) =
            If <$> traverse (uniqueBranch . fmap resolveBranch) branches
               <*> traverse (uniqueStatements . (resolveStatements scope <$>)) fallback
            where resolveBranch (Rank2A.Pair condition action) =
                     Rank2A.Pair <$> uniqueExpression (resolveExpression scope <$> condition)
                                 <*> uniqueStatements (resolveStatements scope <$> action)
         resolveStatement scope (CaseStatement expression cases fallback) =
            CaseStatement <$> uniqueExpression (resolveExpression scope <$> expression)
                          <*> traverse (uniqueCase . fmap resolveCase) cases
                          <*> traverse (uniqueStatements . (resolveStatements scope <$>)) fallback
            where resolveCase (Case caseLabels action) =
                     Case <$> traverse (uniqueLabels . fmap resolveLabels) caseLabels
                          <*> uniqueStatements (resolveStatements scope <$> action)
                  resolveCase EmptyCase = pure EmptyCase
                  resolveLabels (SingleLabel expression) =
                     SingleLabel <$> uniqueExpression (resolveExpression scope <$> expression)
                  resolveLabels (LabelRange low high) =
                     LabelRange <$> uniqueExpression (resolveExpression scope <$> low)
                                <*> uniqueExpression (resolveExpression scope <$> high)
         resolveStatement scope (While condition body) =
            While <$> uniqueExpression (resolveExpression scope <$> condition)
                  <*> uniqueStatements (resolveStatements scope <$> body)
         resolveStatement scope (Repeat body condition) =
            Repeat <$> uniqueStatements (resolveStatements scope <$> body)
                   <*> uniqueExpression (resolveExpression scope <$> condition)
         resolveStatement scope (For index from to by body) =
            For index <$> uniqueExpression (resolveExpression scope <$> from)
                      <*> uniqueExpression (resolveExpression scope <$> to)
                      <*> traverse (uniqueExpression . (resolveExpression scope <$>)) by
                      <*> uniqueStatements (resolveStatements scope <$> body)
         resolveStatement scope (Loop body) = Loop <$> uniqueStatements (resolveStatements scope <$> body)
         resolveStatement scope (With alternatives fallback) =
            With <$> traverse (uniqueWithAlternative . (resolveAlt <$>)) alternatives
                 <*> traverse (uniqueStatements . (resolveStatements scope <$>)) fallback
            where resolveAlt (WithAlternative name t action) =
                     WithAlternative name t <$> uniqueStatements (resolveStatements scope <$> action)
         resolveStatement scope Exit = pure Exit
         resolveStatement scope (Return expression) =
            Return <$> traverse (uniqueExpression . (resolveExpression scope <$>)) expression

         resolveExpression scope (Relation Is left (Ambiguous rights)) =
            Relation Is <$> uniqueExpression (resolveExpression scope <$> left)
                        <*> (typeToValue <$> sconcat (expressionToType <$> rights))
            where typeToValue (TypeReference n) = Identity (Read (Identity (Variable n)))
                  expressionToType (Read (Ambiguous d)) = sconcat (designatorToType <$> d)
                  designatorToType (Variable q) = resolveType scope (TypeReference q)
                  designatorToType d = Failure (NotATypeDesignator d :| [])
         resolveExpression scope (Relation op left right) =
            Relation op <$> uniqueExpression (resolveExpression scope <$> left)
                        <*> uniqueExpression (resolveExpression scope <$> right)
         resolveExpression scope (Positive e) = Positive <$> uniqueExpression (resolveExpression scope <$> e)
         resolveExpression scope (Negative e) = Negative <$> uniqueExpression (resolveExpression scope <$> e)
         resolveExpression scope (Add left right) =
            Add <$> uniqueExpression (resolveExpression scope <$> left)
                <*> uniqueExpression (resolveExpression scope <$> right)
         resolveExpression scope (Subtract left right) =
            Subtract <$> uniqueExpression (resolveExpression scope <$> left)
                     <*> uniqueExpression (resolveExpression scope <$> right)
         resolveExpression scope (Or left right) =
            Or <$> uniqueExpression (resolveExpression scope <$> left)
               <*> uniqueExpression (resolveExpression scope <$> right)
         resolveExpression scope (Multiply left right) =
            Multiply <$> uniqueExpression (resolveExpression scope <$> left)
                     <*> uniqueExpression (resolveExpression scope <$> right)
         resolveExpression scope (Divide left right) =
            Divide <$> uniqueExpression (resolveExpression scope <$> left)
                   <*> uniqueExpression (resolveExpression scope <$> right)
         resolveExpression scope (IntegerDivide left right) =
            IntegerDivide <$> uniqueExpression (resolveExpression scope <$> left)
                          <*> uniqueExpression (resolveExpression scope <$> right)
         resolveExpression scope (Modulo left right) = 
            Modulo <$> uniqueExpression (resolveExpression scope <$> left)
                   <*> uniqueExpression (resolveExpression scope <$> right)
         resolveExpression scope (And left right) =
            And <$> uniqueExpression (resolveExpression scope <$> left)
                <*> uniqueExpression (resolveExpression scope <$> right)
         resolveExpression scope (Integer x) = pure (Integer x)
         resolveExpression scope (Real x) = pure (Real x)
         resolveExpression scope (CharConstant x) = pure (CharConstant x)
         resolveExpression scope (CharCode x) = pure (CharCode x)
         resolveExpression scope (String x) = pure (String x)
         resolveExpression scope Nil = pure Nil
         resolveExpression scope (Set elements) =
            Set <$> traverse (uniqueElement . (resolveElement scope <$>)) elements
         resolveExpression scope (Read designators) =
            Read <$> uniqueDesignator (resolveDesignator scope <$> designators)
         resolveExpression scope (FunctionCall functions parameters)
            | Success (Identity (Variable q)) <- uniqueDesignator (resolveProcedure scope <$> functions),
              Success (DeclaredProcedure True _) <- resolveName scope q =
                 FunctionCall (Identity $ Variable q)
                 <$> traverse (uniqueExpression . (resolveExpressionOrType scope <$>)) parameters
            | otherwise =
                 FunctionCall
                 <$> uniqueDesignator (resolveProcedure scope <$> functions)
                 <*> traverse (uniqueExpression . (resolveExpression scope <$>)) parameters
         resolveExpression scope (Not e) = Negative <$> uniqueExpression (resolveExpression scope <$> e)

         resolveExpressionOrType scope (Read designators) =
            Read <$> uniqueDesignator (resolveDesignatorOrType scope <$> designators)
         resolveExpressionOrType scope e = resolveExpression scope e

         resolveDesignatorOrType scope (Variable q)
            | Success DeclaredType{} <- resolveName scope q = Success (Variable q)
         resolveDesignatorOrType scope e = resolveDesignator scope e

         resolveElement scope (Element e) = Element <$> uniqueExpression (resolveExpression scope <$> e)
         resolveElement scope (Range left right) =
            Range <$> uniqueExpression (resolveExpression scope <$> left)
                  <*> uniqueExpression (resolveExpression scope <$> right)

         resolveDesignator scope (Variable q) =
            case resolveName scope q
            of Failure err ->  Failure err
               Success DeclaredType{} -> Failure (NotAValue q :| [])
               Success _ -> Success (Variable q)
         resolveDesignator scope (Field record field) =
            Field <$> uniqueDesignator (resolveRecord scope <$> record) <*> pure field
         resolveDesignator scope (Index array indexes) =
            Index <$> uniqueDesignator (resolveArray scope <$> array)
                  <*> traverse (uniqueExpression . (resolveExpression scope <$>)) indexes
         resolveDesignator scope (TypeGuard designator subtype) =
            TypeGuard <$> uniqueDesignator (resolveRecord scope <$> designator)
                      <*> resolveTypeName scope subtype
         resolveDesignator scope (Dereference pointer) =
            Dereference <$> uniqueDesignator (resolvePointer scope <$> pointer)

         resolveTypeName scope q =
            case resolveName scope q
            of Failure err ->  Failure err
               Success DeclaredType{} -> Success q
               Success _ -> Failure (NotAType q :| [])

         resolveBaseType scope t = case resolveType scope t
                                   of Failure err -> Failure err
                                      Success t' -> resolveTypeReference scope t'

         resolveProcedure scope d@(Variable q) =
            case resolveName scope q
            of Failure err ->  Failure err
               Success DeclaredType{} -> Failure (NotAValue q :| [])
               Success DeclaredProcedure{} -> resolveDesignator scope d
               Success (DeclaredVariable (Identity t))
                  | Success ProcedureType{} <- resolveTypeReference scope t -> resolveDesignator scope d
                  | otherwise -> Failure (NotAProcedure q :| [])
         resolveProcedure scope d = resolveDesignator scope d

         resolveWriteable scope d@(Variable q) =
            case resolveName scope q
            of Failure err ->  Failure err
               Success DeclaredType{} -> Failure (NotAValue q :| [])
               Success DeclaredProcedure{} -> Failure (NotWriteable q :| [])
               Success DeclaredConstant{} -> Failure (NotWriteable q :| [])
               Success DeclaredVariable{} -> resolveDesignator scope d
         resolveWriteable scope d = resolveDesignator scope d

         resolveRecord scope d@(Variable q) =
            case resolveName scope q
            of Failure err ->  Failure err
               Success DeclaredType{} -> Failure (NotAValue q :| [])
               Success DeclaredProcedure{} -> Failure (NotAValue q :| [])
               Success (DeclaredVariable t) -> resolveDesignator scope d
         resolveRecord scope d = resolveDesignator scope d

         resolveArray = resolveDesignator
         resolvePointer = resolveDesignator

         resolveName scope q@(QualIdent moduleName name) =
            case Map.lookup moduleName moduleExports
            of Nothing -> Failure (UnknownModule moduleName :| [])
               Just exports -> case Map.lookup name exports
                               of Just (Success rhs) -> Success rhs
                                  Just (Failure err) -> Failure err
                                  Nothing -> Failure (UnknownImport q :| [])
         resolveName scope (NonQualIdent name) =
            case Map.lookup name scope
            of Just (Success rhs) -> Success rhs
               _ -> Failure (UnknownLocal name :| [])
               
         resolveBinding scope (DeclaredConstant expression) =
            DeclaredConstant <$> uniqueExpression (resolveExpression scope <$> expression)
         resolveBinding scope (DeclaredType typeDef) =
            DeclaredType <$> uniqueType (resolveBaseType scope <$> typeDef)
         resolveBinding scope (DeclaredVariable typeDef) =
            DeclaredVariable <$> uniqueType (resolveBaseType scope <$> typeDef)
         resolveBinding scope (DeclaredProcedure special parameters) =
            DeclaredProcedure special <$> traverse (uniqueParameters . (resolveParameters scope <$>)) parameters
         
declarationBinding :: Ident -> Declaration f f -> [(Ident, (AccessMode, DeclarationRHS f))]
declarationBinding _ (ConstantDeclaration (IdentDef name export) expr) =
   [(name, (export, DeclaredConstant expr))]
declarationBinding _ (TypeDeclaration (IdentDef name export) typeDef) =
   [(name, (export, DeclaredType typeDef))]
declarationBinding _ (VariableDeclaration names typeDef) =
   [(name, (export, DeclaredVariable typeDef)) | (IdentDef name export) <- NonEmpty.toList names]
declarationBinding moduleName (ProcedureDeclaration (ProcedureHeading _ _ (IdentDef name export) parameters) _ _) =
   [(name, (export, DeclaredProcedure (moduleName == "SYSTEM") parameters))]
declarationBinding _ (ForwardDeclaration (IdentDef name export) parameters) =
   [(name, (export, DeclaredProcedure False parameters))]

predefined, predefined2 :: Predefined
-- | The set of 'Predefined' types and procedures defined in the Oberon Language Report.
predefined = Success <$> Map.fromList
   [("BOOLEAN", DeclaredType (Identity $ TypeReference $ NonQualIdent "BOOLEAN")),
    ("CHAR", DeclaredType (Identity $ TypeReference $ NonQualIdent "CHAR")),
    ("SHORTINT", DeclaredType (Identity $ TypeReference $ NonQualIdent "SHORTINT")),
    ("INTEGER", DeclaredType (Identity $ TypeReference $ NonQualIdent "INTEGER")),
    ("LONGINT", DeclaredType (Identity $ TypeReference $ NonQualIdent "LONGINT")),
    ("REAL", DeclaredType (Identity $ TypeReference $ NonQualIdent "REAL")),
    ("LONGREAL", DeclaredType (Identity $ TypeReference $ NonQualIdent "LONGREAL")),
    ("SET", DeclaredType (Identity $ TypeReference $ NonQualIdent "SET")),
    ("TRUE", DeclaredConstant (Identity $ Read $ Identity $ Variable $ NonQualIdent "TRUE")),
    ("FALSE", DeclaredConstant (Identity $ Read $ Identity $ Variable $ NonQualIdent "FALSE")),
    ("ABS", DeclaredProcedure False $ Just $ Identity $
            FormalParameters [Identity $ FPSection False (pure "n") $ Identity $ TypeReference $ NonQualIdent "INTEGER"] $
            Just $ NonQualIdent "INTEGER"),
    ("ASH", DeclaredProcedure False $ Just $ Identity $
            FormalParameters [Identity $ FPSection False (pure "n") $ Identity $ TypeReference $ NonQualIdent "INTEGER"] $
            Just $ NonQualIdent "INTEGER"),
    ("CAP", DeclaredProcedure False $ Just $ Identity $
            FormalParameters [Identity $ FPSection False (pure "c") $ Identity $ TypeReference $ NonQualIdent "INTEGER"] $
            Just $ NonQualIdent "CAP"),
    ("LEN", DeclaredProcedure False $ Just $ Identity $
            FormalParameters [Identity $ FPSection False (pure "c") $ Identity $ TypeReference $ NonQualIdent "ARRAY"] $
            Just $ NonQualIdent "LONGINT"),
    ("MAX", DeclaredProcedure True $ Just $ Identity $
            FormalParameters [Identity $ FPSection False (pure "c") $ Identity $ TypeReference $ NonQualIdent "SET"] $
            Just $ NonQualIdent "INTEGER"),
    ("MIN", DeclaredProcedure True $ Just $ Identity $
            FormalParameters [Identity $ FPSection False (pure "c") $ Identity $ TypeReference $ NonQualIdent "SET"] $
            Just $ NonQualIdent "INTEGER"),
    ("ODD", DeclaredProcedure False $ Just $ Identity $
            FormalParameters [Identity $ FPSection False (pure "n") $ Identity $ TypeReference $ NonQualIdent "CHAR"] $
            Just $ NonQualIdent "BOOLEAN"),
    ("SIZE", DeclaredProcedure True $ Just $ Identity $
             FormalParameters [Identity $ FPSection False (pure "n") $ Identity $ TypeReference $ NonQualIdent "CHAR"] $
             Just $ NonQualIdent "INTEGER"),
    ("ORD", DeclaredProcedure False $ Just $ Identity $
            FormalParameters [Identity $ FPSection False (pure "n") $ Identity $ TypeReference $ NonQualIdent "CHAR"] $
            Just $ NonQualIdent "INTEGER"),
    ("CHR", DeclaredProcedure False $ Just $ Identity $
            FormalParameters [Identity $ FPSection False (pure "n") $ Identity $ TypeReference $ NonQualIdent "INTEGER"] $
            Just $ NonQualIdent "CHAR"),
    ("SHORT", DeclaredProcedure False $ Just $ Identity $
              FormalParameters [Identity $ FPSection False (pure "n") $ Identity $ TypeReference $ NonQualIdent "INTEGER"] $
              Just $ NonQualIdent "INTEGER"),
    ("LONG", DeclaredProcedure False $ Just $ Identity $
             FormalParameters [Identity $ FPSection False (pure "n") $ Identity $ TypeReference $ NonQualIdent "INTEGER"] $
             Just $ NonQualIdent "INTEGER"),
    ("ENTIER", DeclaredProcedure False $ Just $ Identity $
               FormalParameters [Identity $ FPSection False (pure "n") $ Identity $ TypeReference $ NonQualIdent "REAL"] $
               Just $ NonQualIdent "INTEGER"),
    ("INC", DeclaredProcedure False $ Just $ Identity $
            FormalParameters [Identity $ FPSection False (pure "n") $ Identity $ TypeReference $ NonQualIdent "INTEGER"] Nothing),
    ("DEC", DeclaredProcedure False $ Just $ Identity $
            FormalParameters [Identity $ FPSection False (pure "n") $ Identity $ TypeReference $ NonQualIdent "INTEGER"] Nothing),
    ("INCL", DeclaredProcedure False $ Just $ Identity $
             FormalParameters [Identity $ FPSection False (pure "s") $ Identity $ TypeReference $ NonQualIdent "SET",
                               Identity $ FPSection False (pure "n") $ Identity $ TypeReference $ NonQualIdent "INTEGER"] Nothing),
    ("EXCL", DeclaredProcedure False $ Just $ Identity $
             FormalParameters [Identity $ FPSection False (pure "s") $ Identity $ TypeReference $ NonQualIdent "SET",
                               Identity $ FPSection False (pure "n") $ Identity $ TypeReference $ NonQualIdent "INTEGER"] Nothing),
    ("COPY", DeclaredProcedure False $ Just $ Identity $
             FormalParameters [Identity $ FPSection False (pure "s") $ Identity $ TypeReference $ NonQualIdent "ARRAY",
                               Identity $ FPSection False (pure "n") $ Identity $ TypeReference $ NonQualIdent "ARRAY"] Nothing),
    ("NEW", DeclaredProcedure False $ Just $ Identity $
            FormalParameters [Identity $ FPSection False (pure "n") $ Identity $ TypeReference $ NonQualIdent "POINTER"] Nothing),
    ("HALT", DeclaredProcedure False $ Just $ Identity $
             FormalParameters [Identity $ FPSection False (pure "n") $ Identity $ TypeReference $ NonQualIdent "INTEGER"] Nothing)]

-- | The set of 'Predefined' types and procedures defined in the Oberon-2 Language Report.
predefined2 = predefined <>
   (Success <$> Map.fromList
    [("ASSERT", DeclaredProcedure False $ Just $ Identity $
             FormalParameters [Identity $ FPSection False (pure "s") $ Identity $ TypeReference $ NonQualIdent "ARRAY",
                               Identity $ FPSection False (pure "n") $ Identity $ TypeReference $ NonQualIdent "ARRAY"] Nothing)])

resolveTypeReferenceIn scope (DeclaredType (Identity t)) = DeclaredType . Identity <$> resolveTypeReference scope t
resolveTypeReferenceIn scope (DeclaredVariable (Identity t)) = 
   DeclaredVariable . Identity <$> resolveTypeReference scope t
resolveTypeReferenceIn scope d = pure d

resolveTypeReference :: Map Ident (Validation (NonEmpty Error) (DeclarationRHS Identity)) -> Type Identity Identity
                        -> Validation (NonEmpty Error) (Type Identity Identity)
resolveTypeReference scope t@(TypeReference q@(NonQualIdent name)) =
   case Map.lookup name scope
   of Nothing -> pure t
      Just (Failure err) ->  Failure err
      Just (Success (DeclaredType (Identity t'@(TypeReference q'))))
         | q == q' -> pure t' -- built-in type
      Just (Success (DeclaredType (Identity t'))) -> resolveTypeReference scope t'
      Just {} -> Failure (NotAType q :| [])
resolveTypeReference scope t = pure t

exportsOfModule :: Module Identity Identity -> Scope
exportsOfModule = Map.mapMaybe isExported . globalsOfModule
   where isExported (PrivateOnly, _) = Nothing
         isExported (_, binding) = Just binding

globalsOfModule :: Module Identity Identity 
                   -> Map Ident (AccessMode, Validation (NonEmpty Error) (DeclarationRHS Identity))
globalsOfModule (Module name imports declarations _ _) = scope
   where scope = (resolveTypeReferenceIn scope' <$>) <$> Map.fromList declarationBindings
         scope' = snd <$> scope
         declarationBindings = concatMap (declarationBinding name . runIdentity) declarations

uniqueBinding = unique InvalidDeclaration AmbiguousBinding
uniqueBranch = unique InvalidStatement AmbiguousBranch
uniqueCase = unique InvalidStatement AmbiguousCase
uniqueDeclaration = unique InvalidDeclaration AmbiguousDeclaration
uniqueDesignator = unique InvalidDesignator AmbiguousDesignator
uniqueExpression = unique InvalidExpression AmbiguousExpression
uniqueElement = unique InvalidExpression AmbiguousElement
uniqueFields = unique InvalidExpression AmbiguousFields
uniqueLabels = unique InvalidExpression AmbiguousLabels
uniqueParameters = unique InvalidDeclaration AmbiguousParameters
uniqueSection = unique InvalidStatement AmbiguousSection
uniqueStatement = unique InvalidStatement AmbiguousStatement
uniqueStatements = unique InvalidStatement AmbiguousStatements
uniqueType = unique InvalidDeclaration AmbiguousType
uniqueWithAlternative = unique InvalidStatement AmbiguousWithAlternative

unique :: (NonEmpty Error -> Error) -> ([a] -> Error) 
          -> Ambiguous (Validation (NonEmpty Error) a) -> Validation (NonEmpty Error) (Identity a)
unique _ _ (Ambiguous (x :| [])) = Identity <$> x
unique inv amb (Ambiguous xs) = 
   case partitionEithers (validationToEither <$> NonEmpty.toList xs)
   of (_, [x]) -> Success (Identity x)
      (errors, []) -> Failure (inv (sconcat $ NonEmpty.fromList errors) :| [])
      (_, stats) -> Failure (amb stats :| [])
