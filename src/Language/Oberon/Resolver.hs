{-# LANGUAGE FlexibleContexts, FlexibleInstances, KindSignatures, MultiParamTypeClasses,
             OverloadedStrings, ScopedTypeVariables, StandaloneDeriving, TemplateHaskell, UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}

-- | This module exports functions for resolving the syntactic ambiguities in a parsed module. For example, an Oberon
-- expression @foo(bar)@ may be a call to function @foo@ with a parameter @bar@, or it may be type guard on variable
-- @foo@ casting it to type @bar@.

module Language.Oberon.Resolver (Error(..),
                                 Predefined, predefined, predefined2, resolveModule, resolveModules) where

import Control.Applicative (Alternative)
import Control.Monad ((>=>))
import Control.Monad.Trans.State (StateT(..), evalStateT)
import Data.Either (partitionEithers)
import Data.Either.Validation (Validation(..), validationToEither)
import Data.Foldable (toList)
import Data.Functor.Identity (Identity(..))
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.List as List
import Data.Monoid (Alt(..))
import Data.Map.Lazy (Map, traverseWithKey)
import qualified Data.Map.Lazy as Map
import Data.Semigroup (Semigroup(..), sconcat)

import qualified Transformation as Shallow
import qualified Transformation.Deep as Deep
import qualified Transformation.Deep.TH
import qualified Transformation.Rank2 as Rank2
import Text.Grampa (Ambiguous(..), ParseFailure)

import Language.Oberon.AST

data DeclarationRHS f' f = DeclaredConstant (f (ConstExpression f' f'))
                         | DeclaredType (f (Type f' f'))
                         | DeclaredVariable (f (Type f' f'))
                         | DeclaredProcedure Bool (Maybe (f (FormalParameters f' f')))
deriving instance Show (DeclarationRHS Identity Identity)
deriving instance Show (DeclarationRHS Ambiguous Ambiguous)

-- | All possible resolution errors
data Error = UnknownModule QualIdent
           | UnknownLocal Ident
           | UnknownImport QualIdent
           | AmbiguousParses
           | AmbiguousDeclaration [Declaration Ambiguous Ambiguous]
           | AmbiguousDesignator [Designator Ambiguous Ambiguous]
           | AmbiguousExpression [Expression Ambiguous Ambiguous]
           | AmbiguousRecord [Designator Ambiguous Ambiguous]
           | AmbiguousStatement [Statement Ambiguous Ambiguous]
           | InvalidExpression (NonEmpty Error)
           | InvalidFunctionParameters [Ambiguous (Expression Ambiguous Ambiguous)]
           | InvalidRecord (NonEmpty Error)
           | InvalidStatement (NonEmpty Error)
           | NotARecord QualIdent
           | NotAType QualIdent
           | NotAValue QualIdent
           | ClashingImports
           | UnparseableModule ParseFailure
           deriving (Show)

type Scope = Map Ident (Validation (NonEmpty Error) (DeclarationRHS Identity Identity))

-- | A set of predefined declarations.
type Predefined = Scope

data Resolution = Resolution{_modules :: Map Ident Scope}

type Resolved = StateT (Scope, ResolutionState) (Validation (NonEmpty Error))

data ResolutionState = ModuleState
                     | DeclarationState
                     | StatementState
                     | ExpressionState
                     | ExpressionOrTypeState
                     deriving (Eq, Show)

instance Monad (Validation (NonEmpty Error)) where
   Success s >>= f = f s
   Failure errors >>= _ = Failure errors

instance Shallow.Functor Resolution Ambiguous Resolved (Module Resolved Resolved) where
   (<$>) = mapResolveDefault

instance {-# overlappable #-} Show (g Identity Identity) =>
                              Shallow.Traversable Resolution Ambiguous Identity Resolved (g Identity Identity) where
   traverse = traverseResolveDefault

instance {-# overlappable #-} Show (g Ambiguous Ambiguous) =>
                              Shallow.Traversable Resolution Ambiguous Identity Resolved (g Ambiguous Ambiguous) where
   traverse = traverseResolveDefault

instance {-# overlaps #-} Shallow.Traversable
                          Resolution Ambiguous Identity Resolved (Designator Ambiguous Ambiguous) where
   traverse res (Ambiguous designators) = StateT $ \s@(scope, state)->
      case partitionEithers (NonEmpty.toList (validationToEither . resolveDesignator res scope state <$> designators))
      of (_, [x]) -> Success (Identity x, s)
         (errors, []) -> Failure (sconcat $ NonEmpty.fromList errors)
         (_, multi) -> Failure (AmbiguousDesignator multi :| [])

instance {-# overlaps #-} Shallow.Traversable
                          Resolution Ambiguous Identity Resolved (Expression Ambiguous Ambiguous) where
   traverse res expressions = StateT $ \s@(scope, state)->
      let resolveExpression :: Expression Ambiguous Ambiguous
                            -> Validation (NonEmpty Error) (Expression Ambiguous Ambiguous, ResolutionState)
          resolveExpression e@(Read designators) =
             case evalStateT (Shallow.traverse res designators) s
             of Failure errors -> Failure errors
                Success{} -> pure (e, state)
          resolveExpression e@(FunctionCall functions parameters) =
             case evalStateT (Shallow.traverse res functions) s
             of Failure errors -> Failure errors
                Success (Identity d)
                   | Variable q <- d, Success (DeclaredProcedure True _) <- resolveName res scope q
                     -> pure (e, ExpressionOrTypeState)
                   | Success{} <- evalStateT (traverse (Shallow.traverse res) parameters) (scope, ExpressionState)
                     -> pure (e, ExpressionState)
                   | otherwise -> Failure (pure $ InvalidFunctionParameters parameters)
          resolveExpression e@(Relation Is lefts rights) = pure (e, ExpressionOrTypeState)
          resolveExpression e = pure (e, state)
      in (\(r, s)-> (Identity r, (scope, s)))
         <$> unique InvalidExpression (AmbiguousExpression . (fst <$>)) (resolveExpression <$> expressions)

instance {-# overlaps #-} Shallow.Traversable
                          Resolution Ambiguous Identity Resolved (Declaration Ambiguous Ambiguous) where
   traverse res (Ambiguous (proc@(ProcedureDeclaration heading body _) :| [])) =
      StateT $ \s@(scope, state)->
         let ProcedureHeading receiver _indirect _name parameters = heading
             ProcedureBody declarations statements = body
             innerScope = localScope res "" declarations (parameterScope `Map.union` receiverScope `Map.union` scope)
             receiverScope = maybe mempty receiverBinding receiver
             receiverBinding (_, name, ty) = Map.singleton name (Success $ DeclaredVariable $ pure $ TypeReference
                                                                 $ NonQualIdent ty)
             parameterScope = case parameters
                              of Nothing -> mempty
                                 Just (Ambiguous (FormalParameters sections _ :| []))
                                    -> Map.fromList (concatMap binding sections)
             binding (Ambiguous (FPSection _ names types :| [])) =
                [(v, evalStateT (Deep.traverseDown res $ DeclaredVariable types) s) | v <- NonEmpty.toList names]
         in Success (Identity proc, (innerScope, state))
   traverse res (Ambiguous (dec :| [])) = pure (Identity dec)
   traverse _ declarations = StateT (const $ Failure $ pure $ AmbiguousDeclaration $ toList declarations)

instance {-# overlaps #-} Shallow.Traversable
                          Resolution Ambiguous Identity Resolved (ProcedureBody Ambiguous Ambiguous) where
   traverse res (Ambiguous (body@(ProcedureBody declarations statements) :| [])) = StateT $ \(scope, state)->
      Success (Identity body, (localScope res "" declarations scope, state))
   traverse _ b = StateT (const $ Failure $ pure AmbiguousParses)

instance {-# overlaps #-} Shallow.Traversable
                          Resolution Ambiguous Identity Resolved (Statement Ambiguous Ambiguous) where
   traverse res statements = StateT $ \s@(scope, state)->
      let resolveStatement :: Statement Ambiguous Ambiguous
                            -> Validation (NonEmpty Error) (Statement Ambiguous Ambiguous, ResolutionState)
          resolveStatement p@(ProcedureCall procedures parameters) =
             case evalStateT (Shallow.traverse res procedures) s
             of Failure errors -> Failure errors
                Success{} -> pure (p, StatementState)
          resolveStatement stat = pure (stat, StatementState)
      in (\(r, s)-> (Identity r, (scope, s)))
         <$> unique InvalidStatement (AmbiguousStatement . (fst <$>)) (resolveStatement <$> statements)

mapResolveDefault :: Resolution -> Ambiguous (g Resolved Resolved) -> Resolved (g Resolved Resolved)
mapResolveDefault Resolution{} (Ambiguous (x :| [])) = pure x
mapResolveDefault Resolution{} _ = StateT (const $ Failure $ pure AmbiguousParses)

traverseResolveDefault :: Show (g f f) => Resolution -> Ambiguous (g (f :: * -> *) f) -> Resolved (Identity (g f f))
traverseResolveDefault Resolution{} (Ambiguous (x :| [])) = StateT (\s-> Success (Identity x, s))
traverseResolveDefault Resolution{} x@(Ambiguous _) = StateT (const $ Failure $ pure AmbiguousParses)

resolveDesignator :: Resolution -> Scope -> ResolutionState -> Designator Ambiguous Ambiguous
                  -> Validation (NonEmpty Error) (Designator Ambiguous Ambiguous)
resolveDesignator res scope state = resolveDesignator'
   where resolveTypeName   :: QualIdent -> Validation (NonEmpty Error) QualIdent
         resolveDesignator' (Variable q) =
            case resolveName res scope q
            of Failure err ->  Failure err
               Success DeclaredType{} | state /= ExpressionOrTypeState -> Failure (NotAValue q :| [])
               Success _ -> Success (Variable q)
         resolveDesignator' d@(Field records field) =
            case evalStateT (Shallow.traverse res records) (scope, state)
            of Failure errors -> Failure errors
               Success{} -> pure d
         resolveDesignator' (TypeGuard records subtypes) =
            case unique InvalidRecord AmbiguousRecord (resolveRecord <$> records)
            of Failure errors -> Failure errors
               Success{} -> TypeGuard records <$> resolveTypeName subtypes
         resolveDesignator' d@(Dereference pointers) =
            case evalStateT (Shallow.traverse res pointers) (scope, state)
            of Failure errors -> Failure errors
               Success{} -> pure d
         resolveDesignator' d = pure d
         resolveRecord d@(Variable q) =
            case resolveName res scope q
            of Failure err -> Failure err
               Success DeclaredType{} -> Failure (NotAValue q :| [])
               Success DeclaredProcedure{} -> Failure (NotARecord q :| [])
               Success (DeclaredVariable t) -> resolveDesignator' d
         resolveRecord d = resolveDesignator' d

         resolveTypeName q =
            case resolveName res scope q
            of Failure err ->  Failure err
               Success DeclaredType{} -> Success q
               Success _ -> Failure (NotAType q :| [])

resolveName :: Resolution -> Scope -> QualIdent -> Validation (NonEmpty Error) (DeclarationRHS Identity Identity)
resolveName res scope q@(QualIdent moduleName name) =
   case Map.lookup moduleName (_modules res)
   of Nothing -> Failure (UnknownModule q :| [])
      Just exports -> case Map.lookup name exports
                      of Just rhs -> rhs
                         Nothing -> Failure (UnknownImport q :| [])
resolveName res scope (NonQualIdent name) =
   case Map.lookup name scope
   of Just (Success rhs) -> Success rhs
      _ -> Failure (UnknownLocal name :| [])

resolveModules :: Predefined -> Map Ident (Module Ambiguous Ambiguous)
                -> Validation (NonEmpty (Ident, NonEmpty Error)) (Map Ident (Module Identity Identity))
resolveModules predefinedScope modules = traverseWithKey extractErrors modules'
   where modules' = resolveModule predefinedScope modules' <$> modules
         extractErrors moduleKey (Failure e)   = Failure ((moduleKey, e) :| [])
         extractErrors _         (Success mod) = Success mod

resolveModule :: Scope -> Map Ident (Validation (NonEmpty Error) (Module Identity Identity))
               -> Module Ambiguous Ambiguous -> Validation (NonEmpty Error) (Module Identity Identity)
resolveModule predefined modules m@(Module moduleName imports declarations body _) =
   evalStateT (Deep.traverseDown res m) (moduleGlobalScope, ModuleState)
   where res = Resolution moduleExports
         importedModules = Map.delete mempty (Map.mapKeysWith clashingRenames importedAs modules)
            where importedAs moduleName = case List.find ((== moduleName) . snd) imports
                                          of Just (Nothing, moduleKey) -> moduleKey
                                             Just (Just innerKey, _) -> innerKey
                                             Nothing -> mempty
                  clashingRenames _ _ = Failure (ClashingImports :| [])
         resolveDeclaration :: Ambiguous (Declaration Ambiguous Ambiguous) -> Resolved (Declaration Identity Identity)
         resolveDeclaration d = runIdentity <$> (traverse (Deep.traverseDown res) d >>= Shallow.traverse res)
         moduleExports = foldMap exportsOfModule <$> importedModules
         moduleGlobalScope = localScope res moduleName declarations predefined

localScope :: Resolution -> Ident -> [Ambiguous (Declaration Ambiguous Ambiguous)] -> Scope -> Scope
localScope res qual declarations outerScope = innerScope
   where innerScope = Map.union (snd <$> scopeAdditions) outerScope
         scopeAdditions = (resolveBinding res innerScope <$>)
                          <$> Map.fromList (concatMap (declarationBinding qual . unamb) declarations)
         unamb (Ambiguous (x :| [])) = x
         resolveBinding     :: Resolution -> Scope -> DeclarationRHS Ambiguous Ambiguous
                            -> Validation (NonEmpty Error) (DeclarationRHS Identity Identity)
         resolveBinding res scope dr = evalStateT (Deep.traverseDown res dr) (scope, DeclarationState)

declarationBinding :: Ident -> Declaration f f -> [(Ident, (AccessMode, DeclarationRHS f f))]
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
            FormalParameters [Identity $ FPSection False (pure "c") $ Identity $ TypeReference $ NonQualIdent "CHAR"] $
            Just $ NonQualIdent "CHAR"),
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

exportsOfModule :: Module Identity Identity -> Scope
exportsOfModule = fmap Success . Map.mapMaybe isExported . globalsOfModule
   where isExported (PrivateOnly, _) = Nothing
         isExported (_, binding) = Just binding

globalsOfModule :: Module Identity Identity -> Map Ident (AccessMode, DeclarationRHS Identity Identity)
globalsOfModule (Module name imports declarations _ _) =
   Map.fromList (concatMap (declarationBinding name . runIdentity) declarations)

unique :: (NonEmpty Error -> Error) -> ([a] -> Error) -> Ambiguous (Validation (NonEmpty Error) a)
       -> Validation (NonEmpty Error) a
unique _ _ (Ambiguous (x :| [])) = x
unique inv amb (Ambiguous xs) =
   case partitionEithers (validationToEither <$> NonEmpty.toList xs)
   of (_, [x]) -> Success x
      (errors, []) -> Failure (inv (sconcat $ NonEmpty.fromList errors) :| [])
      (_, multi) -> Failure (amb multi :| [])

$(Transformation.Deep.TH.deriveDownTraversable ''DeclarationRHS)
