{-# Language FlexibleContexts, RecordWildCards, TypeFamilies #-}

module Language.Oberon (parseModule, parseAndResolveModule, parseAndResolveModuleFile,
                        resolvePosition, resolvePositions, Placed, LanguageVersion(..), Options(..)) where

import Language.Oberon.AST (Language, Module(..))
import qualified Language.Oberon.Grammar as Grammar
import qualified Language.Oberon.Resolver as Resolver
import qualified Language.Oberon.ConstantFolder as ConstantFolder
import qualified Language.Oberon.TypeChecker as TypeChecker

import qualified Transformation.Rank2 as Rank2
import qualified Transformation.Deep as Deep

import Control.Monad (guard)
import Data.Either.Validation (Validation(..))
import Data.Functor.Compose (Compose(Compose, getCompose))
import Data.List.NonEmpty (NonEmpty((:|)))
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.Map.Lazy as Map
import Data.Map.Lazy (Map)
import Data.Monoid ((<>))
import Data.Text (Text, unpack)
import Data.Text.IO (readFile)
import Text.Grampa (Ambiguous, Grammar, ParseResults, parseComplete, failureDescription, positionOffset)
import qualified Text.Grampa.ContextFree.LeftRecursive as LeftRecursive
import System.Directory (doesFileExist)
import System.FilePath (FilePath, addExtension, combine, takeDirectory)

import Prelude hiding (readFile)

type NodeWrap = Compose ((,) Int) Ambiguous
type Placed = ((,) Int)

data LanguageVersion = Oberon1 | Oberon2 deriving (Eq, Ord, Show)

data Options = Options{
   foldConstants :: Bool,
   checkTypes :: Bool,
   version :: LanguageVersion}

resolvePositions :: (p ~ Grammar.NodeWrap, q ~ NodeWrap, Deep.Functor (Rank2.Map p q) g)
                 => Text -> g p p -> g q q
resolvePositions src t = resolvePosition src Rank2.<$> t

resolvePosition :: Text -> Grammar.NodeWrap a -> NodeWrap a
resolvePosition src = \(Compose (pos, a))-> Compose (positionOffset src pos, a)

moduleGrammar Oberon1 = Grammar.oberonGrammar
moduleGrammar Oberon2 = Grammar.oberon2Grammar 

definitionGrammar Oberon1 = Grammar.oberonDefinitionGrammar
definitionGrammar Oberon2 = Grammar.oberon2DefinitionGrammar 

-- | Parse the given text of a single module, without resolving the syntactic ambiguities.
parseModule :: LanguageVersion -> Text -> ParseResults [Module Language Language NodeWrap NodeWrap]
parseModule version src =
  getCompose (resolvePositions src <$> Grammar.module_prod (parseComplete (moduleGrammar version) src))

-- | Parse the given text of a single /definition/ module, without resolving the syntactic ambiguities.
parseDefinitionModule :: LanguageVersion -> Text -> ParseResults [Module Language Language NodeWrap NodeWrap]
parseDefinitionModule version src =
  getCompose (resolvePositions src <$> Grammar.module_prod (parseComplete (definitionGrammar version) src))

parseNamedModule :: LanguageVersion -> FilePath -> Text -> IO (ParseResults [Module Language Language NodeWrap NodeWrap])
parseNamedModule version path name =
   do let basePath = combine path (unpack name)
      isDefn <- doesFileExist (addExtension basePath "Def")
      let grammar = (if isDefn then definitionGrammar else moduleGrammar) version
      src <- readFile (addExtension basePath $ if isDefn then "Def" else "Mod")
      return (getCompose $ resolvePositions src <$> Grammar.module_prod (parseComplete grammar src))

parseImportsOf :: LanguageVersion -> FilePath -> Map Text (Module Language Language NodeWrap NodeWrap)
               -> IO (Map Text (Module Language Language NodeWrap NodeWrap))
parseImportsOf version path modules =
   case filter (`Map.notMember` modules) moduleImports
   of [] -> return modules
      newImports -> (((modules <>) . Map.fromList . map assertSuccess) <$>
                     (traverse . traverse) (parseNamedModule version path) [(p, p) | p <- newImports])
                    >>= parseImportsOf version path
   where moduleImports = foldMap importsOf modules
         importsOf (Module _ imports _) = snd <$> imports
         assertSuccess (m, Left err) = error ("Parse error in module " <> unpack m)
         assertSuccess (m, Right [p]) = (m, p)
         assertSuccess (m, Right _) = error ("Ambiguous parses of module " <> unpack m)

-- | Given a directory path for module imports, parse the given module text and all the module files it imports, then
-- use all the information to resolve the syntactic ambiguities.
parseAndResolveModule :: Options -> FilePath -> Text
                      -> IO (Validation (Either (NonEmpty (Resolver.Error Language)) (NonEmpty (TypeChecker.Error Language)))
                                        (Module Language Language Placed Placed))
parseAndResolveModule Options{..} path source =
   case parseModule version source
   of Left err -> return (Failure $ Left $ Resolver.UnparseableModule (failureDescription source err 4) :| [])
      Right [rootModule@(Module moduleName imports _)] ->
         do importedModules <- parseImportsOf version path (Map.singleton moduleName rootModule)
            let resolvedImportMap = Resolver.resolveModule predefinedScope resolvedImportMap <$> importedModules
                predefinedScope = case version 
                                  of Oberon1 -> Resolver.predefined
                                     Oberon2 -> Resolver.predefined2
                successful (Success a) = Just a
                successful _ = Nothing
                addLeft (Failure resolutionErrors) = Failure (Left resolutionErrors)
                addLeft (Success result) = Success result
                constantFolded = ConstantFolder.foldConstants
                                (case version
                                 of Oberon1 -> ConstantFolder.predefined
                                    Oberon2 -> ConstantFolder.predefined2)
                                (Map.mapMaybe successful resolvedImportMap)
                typeErrors = TypeChecker.checkModules
                                (case version 
                                 of Oberon1 -> TypeChecker.predefined
                                    Oberon2 -> TypeChecker.predefined2)
                                constantFolded
            return (if checkTypes && not (null typeErrors)
                    then Failure (Right (NonEmpty.fromList typeErrors))
                    else maybe (addLeft $ resolvedImportMap Map.! moduleName) Success
                         (guard foldConstants *> Map.lookup moduleName constantFolded))
      Right _ -> return (Failure $ Left $ Resolver.AmbiguousParses :| [])

-- | Parse the module file at the given path, assuming all its imports are in the same directory.
parseAndResolveModuleFile :: Options -> FilePath
                          -> IO (Validation (Either (NonEmpty (Resolver.Error Language)) (NonEmpty (TypeChecker.Error Language)))
                                            (Module Language Language Placed Placed))
parseAndResolveModuleFile options path =
  readFile path >>= parseAndResolveModule options (takeDirectory path)
