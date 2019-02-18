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
import Control.Monad.Trans.State (StateT(..), evalStateT, execStateT, get, put)
import Data.Either (partitionEithers)
import Data.Either.Validation (Validation(..), validationToEither)
import Data.Foldable (toList)
import Data.Functor.Compose (Compose(..))
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.List as List
import Data.Monoid (Alt(..))
import Data.Map.Lazy (Map, traverseWithKey)
import qualified Data.Map.Lazy as Map
import Data.Semigroup (Semigroup(..), sconcat)
import Data.Text (Text)

import qualified Rank2.TH
import qualified Transformation as Shallow
import qualified Transformation.Deep as Deep
import qualified Transformation.Deep.TH
import qualified Transformation.Rank2 as Rank2
import Text.Grampa (Ambiguous(..), Position(..), ParseFailure)

import Language.Oberon.AST

data DeclarationRHS f' f = DeclaredConstant (f (ConstExpression f' f'))
                         | DeclaredType (f (Type f' f'))
                         | DeclaredVariable (f (Type f' f'))
                         | DeclaredProcedure Bool (Maybe (f (FormalParameters f' f')))
deriving instance Show (DeclarationRHS Placed Placed)
deriving instance Show (DeclarationRHS NodeWrap NodeWrap)

-- | All possible resolution errors
data Error = UnknownModule QualIdent
           | UnknownLocal Ident
           | UnknownImport QualIdent
           | AmbiguousParses
           | AmbiguousDeclaration [Declaration NodeWrap NodeWrap]
           | AmbiguousDesignator [Designator NodeWrap NodeWrap]
           | AmbiguousExpression [Expression NodeWrap NodeWrap]
           | AmbiguousRecord [Designator NodeWrap NodeWrap]
           | AmbiguousStatement [Statement NodeWrap NodeWrap]
           | InvalidExpression (NonEmpty Error)
           | InvalidFunctionParameters [NodeWrap (Expression NodeWrap NodeWrap)]
           | InvalidRecord (NonEmpty Error)
           | InvalidStatement (NonEmpty Error)
           | NotARecord QualIdent
           | NotAType QualIdent
           | NotAValue QualIdent
           | ClashingImports
           | UnparseableModule Text
           deriving (Show)

type Placed = ((,) Int)
type NodeWrap = Compose Placed Ambiguous

type Scope = Map Ident (Validation (NonEmpty Error) (DeclarationRHS Placed Placed))

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

instance Shallow.Functor Resolution NodeWrap Resolved (Module Resolved Resolved) where
   (<$>) = mapResolveDefault

instance {-# overlappable #-} Show (g Placed Placed) =>
                              Shallow.Traversable Resolution NodeWrap Placed Resolved (g Placed Placed) where
   traverse = traverseResolveDefault

instance {-# overlappable #-} Show (g NodeWrap NodeWrap) =>
                              Shallow.Traversable Resolution NodeWrap Placed Resolved (g NodeWrap NodeWrap) where
   traverse = traverseResolveDefault

instance {-# overlaps #-} Shallow.Traversable
                          Resolution NodeWrap Placed Resolved (Designator NodeWrap NodeWrap) where
   traverse res (Compose (pos, Ambiguous designators)) = StateT $ \s@(scope, state)->
      case partitionEithers (NonEmpty.toList (validationToEither . resolveDesignator res scope state <$> designators))
      of (_, [x]) -> Success ((pos, x), s)
         (errors, []) -> Failure (sconcat $ NonEmpty.fromList errors)
         (_, multi) -> Failure (AmbiguousDesignator multi :| [])

instance {-# overlaps #-} Shallow.Traversable
                          Resolution NodeWrap Placed Resolved (Expression NodeWrap NodeWrap) where
   traverse res expressions = StateT $ \s@(scope, state)->
      let resolveExpression :: Expression NodeWrap NodeWrap
                            -> Validation (NonEmpty Error) (Expression NodeWrap NodeWrap, ResolutionState)
          resolveExpression e@(Read designators) =
             case evalStateT (Shallow.traverse res designators) s
             of Failure errors -> Failure errors
                Success{} -> pure (e, state)
          resolveExpression e@(FunctionCall functions parameters) =
             case evalStateT (Shallow.traverse res functions) s
             of Failure errors -> Failure errors
                Success (pos, d)
                   | Variable q <- d, Success (DeclaredProcedure True _) <- resolveName res scope q
                     -> pure (e, ExpressionOrTypeState)
                   | Success{} <- evalStateT (traverse (Shallow.traverse res) parameters) (scope, ExpressionState)
                     -> pure (e, ExpressionState)
                   | otherwise -> Failure (pure $ InvalidFunctionParameters parameters)
          resolveExpression e@(Relation Is lefts rights) = pure (e, ExpressionOrTypeState)
          resolveExpression e = pure (e, state)
      in (\(pos, (r, s))-> ((pos, r), (scope, s)))
         <$> unique InvalidExpression (AmbiguousExpression . (fst <$>)) (resolveExpression <$> expressions)

instance {-# overlaps #-} Shallow.Traversable
                          Resolution NodeWrap Placed Resolved (Declaration NodeWrap NodeWrap) where
   traverse res (Compose (pos, Ambiguous (proc@(ProcedureDeclaration heading body) :| []))) =
      do s@(scope, state) <- get
         let ProcedureBody declarations statements = body
             Success (headingScope, _) = execStateT (Shallow.traverse res heading) s
             innerScope = localScope res "" declarations (headingScope `Map.union` scope)
         put (innerScope, state)
         return (pos, proc)
   traverse res (Compose (pos, Ambiguous (dec :| []))) = pure (pos, dec)
   traverse _ declarations = StateT (const $ Failure $ pure $ AmbiguousDeclaration $ toList declarations)

instance {-# overlaps #-} Shallow.Traversable
                          Resolution NodeWrap Placed Resolved (ProcedureHeading NodeWrap NodeWrap) where
   traverse res (Compose (pos, Ambiguous (proc@(ProcedureHeading _ _ parameters) :| []))) =
      StateT $ \s@(scope, state)->
         let innerScope = parameterScope `Map.union` scope
             parameterScope = case parameters
                              of Nothing -> mempty
                                 Just (Compose (_, Ambiguous (FormalParameters sections _ :| [])))
                                    -> Map.fromList (concatMap binding sections)
             binding (Compose (_, Ambiguous (FPSection _ names types :| []))) =
                [(v, evalStateT (Deep.traverseDown res $ DeclaredVariable types) s) | v <- NonEmpty.toList names]
         in Success ((pos, proc), (innerScope, state))
   traverse res (Compose (pos, Ambiguous (proc@(TypeBoundHeading var receiverName receiverType _ _ parameters) :| []))) =
      StateT $ \s@(scope, state)->
         let innerScope = parameterScope `Map.union` receiverBinding `Map.union` scope
             receiverBinding :: Map Ident (Validation e (DeclarationRHS f' Placed))
             receiverBinding = Map.singleton receiverName (Success $ DeclaredVariable $ (,) pos $ TypeReference
                                                                 $ NonQualIdent receiverType)
             parameterScope = case parameters
                              of Nothing -> mempty
                                 Just (Compose (_, Ambiguous (FormalParameters sections _ :| [])))
                                    -> Map.fromList (concatMap binding sections)
             binding (Compose (_, Ambiguous (FPSection _ names types :| []))) =
                [(v, evalStateT (Deep.traverseDown res $ DeclaredVariable types) s) | v <- NonEmpty.toList names]
         in Success ((pos, proc), (innerScope, state))

instance {-# overlaps #-} Shallow.Traversable
                          Resolution NodeWrap Placed Resolved (ProcedureBody NodeWrap NodeWrap) where
   traverse res (Compose (pos, Ambiguous (body@(ProcedureBody declarations statements) :| []))) =
     StateT $ \(scope, state)-> Success ((pos, body), (localScope res "" declarations scope, state))
   traverse _ b = StateT (const $ Failure $ pure AmbiguousParses)

instance {-# overlaps #-} Shallow.Traversable
                          Resolution NodeWrap Placed Resolved (Statement NodeWrap NodeWrap) where
   traverse res statements = StateT $ \s@(scope, state)->
      let resolveStatement :: Statement NodeWrap NodeWrap
                            -> Validation (NonEmpty Error) (Statement NodeWrap NodeWrap, ResolutionState)
          resolveStatement p@(ProcedureCall procedures parameters) =
             case evalStateT (Shallow.traverse res procedures) s
             of Failure errors -> Failure errors
                Success{} -> pure (p, StatementState)
          resolveStatement stat = pure (stat, StatementState)
      in (\(pos, (r, s))-> ((pos, r), (scope, s)))
         <$> unique InvalidStatement (AmbiguousStatement . (fst <$>)) (resolveStatement <$> statements)

mapResolveDefault :: Resolution -> NodeWrap (g Resolved Resolved) -> Resolved (g Resolved Resolved)
mapResolveDefault Resolution{} (Compose (_, Ambiguous (x :| []))) = pure x
mapResolveDefault Resolution{} _ = StateT (const $ Failure $ pure AmbiguousParses)

traverseResolveDefault :: Show (g f f) => Resolution -> NodeWrap (g (f :: * -> *) f) -> Resolved (Placed (g f f))
traverseResolveDefault Resolution{} (Compose (pos, Ambiguous (x :| []))) = StateT (\s-> Success ((pos, x), s))
traverseResolveDefault Resolution{} _ = StateT (const $ Failure $ pure AmbiguousParses)

resolveDesignator :: Resolution -> Scope -> ResolutionState -> Designator NodeWrap NodeWrap
                  -> Validation (NonEmpty Error) (Designator NodeWrap NodeWrap)
resolveDesignator res scope state = resolveDesignator'
   where resolveTypeName   :: QualIdent -> Validation (NonEmpty Error) QualIdent
         resolveDesignator',
           resolveRecord :: Designator NodeWrap NodeWrap -> Validation (NonEmpty Error) (Designator NodeWrap NodeWrap)
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

resolveName :: Resolution -> Scope -> QualIdent -> Validation (NonEmpty Error) (DeclarationRHS Placed Placed)
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

resolveModules :: Predefined -> Map Ident (Module NodeWrap NodeWrap)
                -> Validation (NonEmpty (Ident, NonEmpty Error)) (Map Ident (Module Placed Placed))
resolveModules predefinedScope modules = traverseWithKey extractErrors modules'
   where modules' = resolveModule predefinedScope modules' <$> modules
         extractErrors moduleKey (Failure e)   = Failure ((moduleKey, e) :| [])
         extractErrors _         (Success mod) = Success mod

resolveModule :: Scope -> Map Ident (Validation (NonEmpty Error) (Module Placed Placed))
               -> Module NodeWrap NodeWrap -> Validation (NonEmpty Error) (Module Placed Placed)
resolveModule predefined modules m@(Module moduleName imports declarations body) =
   evalStateT (Deep.traverseDown res m) (moduleGlobalScope, ModuleState)
   where res = Resolution moduleExports
         importedModules = Map.delete mempty (Map.mapKeysWith clashingRenames importedAs modules)
            where importedAs moduleName = case List.find ((== moduleName) . snd) imports
                                          of Just (Nothing, moduleKey) -> moduleKey
                                             Just (Just innerKey, _) -> innerKey
                                             Nothing -> mempty
                  clashingRenames _ _ = Failure (ClashingImports :| [])
         resolveDeclaration :: NodeWrap (Declaration NodeWrap NodeWrap) -> Resolved (Declaration Placed Placed)
         resolveDeclaration d = snd <$> (traverse (Deep.traverseDown res) d >>= Shallow.traverse res)
         moduleExports = foldMap exportsOfModule <$> importedModules
         moduleGlobalScope = localScope res moduleName declarations predefined

localScope :: Resolution -> Ident -> [NodeWrap (Declaration NodeWrap NodeWrap)] -> Scope -> Scope
localScope res qual declarations outerScope = innerScope
   where innerScope = Map.union (snd <$> scopeAdditions) outerScope
         scopeAdditions = (resolveBinding res innerScope <$>)
                          <$> Map.fromList (concatMap (declarationBinding qual . unamb) declarations)
         unamb (Compose (offset, Ambiguous (x :| []))) = x
         resolveBinding     :: Resolution -> Scope -> DeclarationRHS NodeWrap NodeWrap
                            -> Validation (NonEmpty Error) (DeclarationRHS Placed Placed)
         resolveBinding res scope dr = evalStateT (Deep.traverseDown res dr) (scope, DeclarationState)

declarationBinding :: Foldable f => Ident -> Declaration f f -> [(Ident, (AccessMode, DeclarationRHS f f))]
declarationBinding _ (ConstantDeclaration (IdentDef name export) expr) =
   [(name, (export, DeclaredConstant expr))]
declarationBinding _ (TypeDeclaration (IdentDef name export) typeDef) =
   [(name, (export, DeclaredType typeDef))]
declarationBinding _ (VariableDeclaration names typeDef) =
   [(name, (export, DeclaredVariable typeDef)) | (IdentDef name export) <- NonEmpty.toList names]
declarationBinding moduleName (ProcedureDeclaration heading _) = procedureHeadBinding (foldr1 const heading)
   where procedureHeadBinding (ProcedureHeading _ (IdentDef name export) parameters) =
            [(name, (export, DeclaredProcedure (moduleName == "SYSTEM") parameters))]
         procedureHeadBinding (TypeBoundHeading _ _ _ _ (IdentDef name export) parameters) =
            [(name, (export, DeclaredProcedure (moduleName == "SYSTEM") parameters))]
declarationBinding _ (ForwardDeclaration (IdentDef name export) parameters) =
   [(name, (export, DeclaredProcedure False parameters))]

predefined, predefined2 :: Predefined
-- | The set of 'Predefined' types and procedures defined in the Oberon Language Report.
predefined = Success <$> Map.fromList
   [("BOOLEAN", DeclaredType ((,) 0 $ TypeReference $ NonQualIdent "BOOLEAN")),
    ("CHAR", DeclaredType ((,) 0 $ TypeReference $ NonQualIdent "CHAR")),
    ("SHORTINT", DeclaredType ((,) 0 $ TypeReference $ NonQualIdent "SHORTINT")),
    ("INTEGER", DeclaredType ((,) 0 $ TypeReference $ NonQualIdent "INTEGER")),
    ("LONGINT", DeclaredType ((,) 0 $ TypeReference $ NonQualIdent "LONGINT")),
    ("REAL", DeclaredType ((,) 0 $ TypeReference $ NonQualIdent "REAL")),
    ("LONGREAL", DeclaredType ((,) 0 $ TypeReference $ NonQualIdent "LONGREAL")),
    ("SET", DeclaredType ((,) 0 $ TypeReference $ NonQualIdent "SET")),
    ("TRUE", DeclaredConstant ((,) 0 $ Read $ (,) 0 $ Variable $ NonQualIdent "TRUE")),
    ("FALSE", DeclaredConstant ((,) 0 $ Read $ (,) 0 $ Variable $ NonQualIdent "FALSE")),
    ("ABS", DeclaredProcedure False $ Just $ (,) 0 $
            FormalParameters [(,) 0 $ FPSection False (pure "n") $ (,) 0 $ TypeReference $ NonQualIdent "INTEGER"] $
            Just $ NonQualIdent "INTEGER"),
    ("ASH", DeclaredProcedure False $ Just $ (,) 0 $
            FormalParameters [(,) 0 $ FPSection False (pure "n") $ (,) 0 $ TypeReference $ NonQualIdent "INTEGER"] $
            Just $ NonQualIdent "INTEGER"),
    ("CAP", DeclaredProcedure False $ Just $ (,) 0 $
            FormalParameters [(,) 0 $ FPSection False (pure "c") $ (,) 0 $ TypeReference $ NonQualIdent "CHAR"] $
            Just $ NonQualIdent "CHAR"),
    ("LEN", DeclaredProcedure False $ Just $ (,) 0 $
            FormalParameters [(,) 0 $ FPSection False (pure "c") $ (,) 0 $ TypeReference $ NonQualIdent "ARRAY"] $
            Just $ NonQualIdent "LONGINT"),
    ("MAX", DeclaredProcedure True $ Just $ (,) 0 $
            FormalParameters [(,) 0 $ FPSection False (pure "c") $ (,) 0 $ TypeReference $ NonQualIdent "SET"] $
            Just $ NonQualIdent "INTEGER"),
    ("MIN", DeclaredProcedure True $ Just $ (,) 0 $
            FormalParameters [(,) 0 $ FPSection False (pure "c") $ (,) 0 $ TypeReference $ NonQualIdent "SET"] $
            Just $ NonQualIdent "INTEGER"),
    ("ODD", DeclaredProcedure False $ Just $ (,) 0 $
            FormalParameters [(,) 0 $ FPSection False (pure "n") $ (,) 0 $ TypeReference $ NonQualIdent "CHAR"] $
            Just $ NonQualIdent "BOOLEAN"),
    ("SIZE", DeclaredProcedure True $ Just $ (,) 0 $
             FormalParameters [(,) 0 $ FPSection False (pure "n") $ (,) 0 $ TypeReference $ NonQualIdent "CHAR"] $
             Just $ NonQualIdent "INTEGER"),
    ("ORD", DeclaredProcedure False $ Just $ (,) 0 $
            FormalParameters [(,) 0 $ FPSection False (pure "n") $ (,) 0 $ TypeReference $ NonQualIdent "CHAR"] $
            Just $ NonQualIdent "INTEGER"),
    ("CHR", DeclaredProcedure False $ Just $ (,) 0 $
            FormalParameters [(,) 0 $ FPSection False (pure "n") $ (,) 0 $ TypeReference $ NonQualIdent "INTEGER"] $
            Just $ NonQualIdent "CHAR"),
    ("SHORT", DeclaredProcedure False $ Just $ (,) 0 $
              FormalParameters [(,) 0 $ FPSection False (pure "n") $ (,) 0 $ TypeReference $ NonQualIdent "INTEGER"] $
              Just $ NonQualIdent "INTEGER"),
    ("LONG", DeclaredProcedure False $ Just $ (,) 0 $
             FormalParameters [(,) 0 $ FPSection False (pure "n") $ (,) 0 $ TypeReference $ NonQualIdent "INTEGER"] $
             Just $ NonQualIdent "INTEGER"),
    ("ENTIER", DeclaredProcedure False $ Just $ (,) 0 $
               FormalParameters [(,) 0 $ FPSection False (pure "n") $ (,) 0 $ TypeReference $ NonQualIdent "REAL"] $
               Just $ NonQualIdent "INTEGER"),
    ("INC", DeclaredProcedure False $ Just $ (,) 0 $
            FormalParameters [(,) 0 $ FPSection False (pure "n") $ (,) 0 $ TypeReference $ NonQualIdent "INTEGER"] Nothing),
    ("DEC", DeclaredProcedure False $ Just $ (,) 0 $
            FormalParameters [(,) 0 $ FPSection False (pure "n") $ (,) 0 $ TypeReference $ NonQualIdent "INTEGER"] Nothing),
    ("INCL", DeclaredProcedure False $ Just $ (,) 0 $
             FormalParameters [(,) 0 $ FPSection False (pure "s") $ (,) 0 $ TypeReference $ NonQualIdent "SET",
                               (,) 0 $ FPSection False (pure "n") $ (,) 0 $ TypeReference $ NonQualIdent "INTEGER"] Nothing),
    ("EXCL", DeclaredProcedure False $ Just $ (,) 0 $
             FormalParameters [(,) 0 $ FPSection False (pure "s") $ (,) 0 $ TypeReference $ NonQualIdent "SET",
                               (,) 0 $ FPSection False (pure "n") $ (,) 0 $ TypeReference $ NonQualIdent "INTEGER"] Nothing),
    ("COPY", DeclaredProcedure False $ Just $ (,) 0 $
             FormalParameters [(,) 0 $ FPSection False (pure "s") $ (,) 0 $ TypeReference $ NonQualIdent "ARRAY",
                               (,) 0 $ FPSection False (pure "n") $ (,) 0 $ TypeReference $ NonQualIdent "ARRAY"] Nothing),
    ("NEW", DeclaredProcedure False $ Just $ (,) 0 $
            FormalParameters [(,) 0 $ FPSection False (pure "n") $ (,) 0 $ TypeReference $ NonQualIdent "POINTER"] Nothing),
    ("HALT", DeclaredProcedure False $ Just $ (,) 0 $
             FormalParameters [(,) 0 $ FPSection False (pure "n") $ (,) 0 $ TypeReference $ NonQualIdent "INTEGER"] Nothing)]

-- | The set of 'Predefined' types and procedures defined in the Oberon-2 Language Report.
predefined2 = predefined <>
   (Success <$> Map.fromList
    [("ASSERT", DeclaredProcedure False $ Just $ (,) 0 $
             FormalParameters [(,) 0 $ FPSection False (pure "s") $ (,) 0 $ TypeReference $ NonQualIdent "ARRAY",
                               (,) 0 $ FPSection False (pure "n") $ (,) 0 $ TypeReference $ NonQualIdent "ARRAY"] Nothing)])

exportsOfModule :: Module Placed Placed -> Scope
exportsOfModule = fmap Success . Map.mapMaybe isExported . globalsOfModule
   where isExported (PrivateOnly, _) = Nothing
         isExported (_, binding) = Just binding

globalsOfModule :: Module Placed Placed -> Map Ident (AccessMode, DeclarationRHS Placed Placed)
globalsOfModule (Module name imports declarations _) =
   Map.fromList (concatMap (declarationBinding name . snd) declarations)

unique :: (NonEmpty Error -> Error) -> ([a] -> Error) -> NodeWrap (Validation (NonEmpty Error) a)
       -> Validation (NonEmpty Error) (Placed a)
unique _ _ (Compose (pos, Ambiguous (x :| []))) = (,) pos <$> x
unique inv amb (Compose (pos, Ambiguous xs)) =
   case partitionEithers (validationToEither <$> NonEmpty.toList xs)
   of (_, [x]) -> Success (pos, x)
      (errors, []) -> Failure (inv (sconcat $ NonEmpty.fromList errors) :| [])
      (_, multi) -> Failure (amb multi :| [])

$(Rank2.TH.deriveFunctor ''DeclarationRHS)
$(Rank2.TH.deriveFoldable ''DeclarationRHS)
$(Rank2.TH.deriveTraversable ''DeclarationRHS)
$(Transformation.Deep.TH.deriveDownTraversable ''DeclarationRHS)
