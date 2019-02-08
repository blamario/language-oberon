{-# Language FlexibleContexts, TypeFamilies #-}
-- | Every function in this module takes a flag that determines whether the input is an Oberon or Oberon-2 module.

module Language.Oberon (parseModule, parseAndResolveModule, parseAndResolveModuleFile,
                        resolvePosition, resolvePositions, Placed) where

import Language.Oberon.AST (Module(..))
import qualified Language.Oberon.Grammar as Grammar
import qualified Language.Oberon.Resolver as Resolver
import qualified Language.Oberon.TypeChecker as TypeChecker

import qualified Transformation.Rank2 as Rank2
import qualified Transformation.Deep as Deep

import Control.Monad (when)
import Data.Either.Validation (Validation(..))
import Data.Functor.Compose (Compose(Compose, getCompose))
import Data.List.NonEmpty (NonEmpty((:|)))
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

resolvePositions :: (p ~ Grammar.NodeWrap, q ~ NodeWrap, Deep.Functor (Rank2.Map p q) g p q)
                 => Text -> g p p -> g q q
resolvePositions src t = resolvePosition src Rank2.<$> t

resolvePosition :: Text -> Grammar.NodeWrap a -> NodeWrap a
resolvePosition src = \(Compose (pos, a))-> Compose (positionOffset src pos, a)

moduleGrammar o2 = if o2 then Grammar.oberon2Grammar else Grammar.oberonGrammar
definitionGrammar o2 = if o2 then Grammar.oberon2DefinitionGrammar else Grammar.oberonDefinitionGrammar

-- | Parse the given text of a single module, without resolving the syntactic ambiguities.
parseModule :: Bool -> Text -> ParseResults [Module NodeWrap NodeWrap]
parseModule oberon2 src =
  getCompose (resolvePositions src <$> Grammar.module_prod (parseComplete (moduleGrammar oberon2) src))

-- | Parse the given text of a single /definition/ module, without resolving the syntactic ambiguities.
parseDefinitionModule :: Bool -> Text -> ParseResults [Module NodeWrap NodeWrap]
parseDefinitionModule oberon2 src =
  getCompose (resolvePositions src <$> Grammar.module_prod (parseComplete (definitionGrammar oberon2) src))

parseNamedModule :: Bool -> FilePath -> Text -> IO (ParseResults [Module NodeWrap NodeWrap])
parseNamedModule oberon2 path name =
   do let basePath = combine path (unpack name)
      isDefn <- doesFileExist (addExtension basePath "Def")
      let grammar = (if isDefn then definitionGrammar else moduleGrammar) oberon2
      src <- readFile (addExtension basePath $ if isDefn then "Def" else "Mod")
      return (getCompose $ resolvePositions src <$> Grammar.module_prod (parseComplete grammar src))

parseImportsOf :: Bool -> FilePath -> Map Text (Module NodeWrap NodeWrap) -> IO (Map Text (Module NodeWrap NodeWrap))
parseImportsOf oberon2 path modules =
   case filter (`Map.notMember` modules) moduleImports
   of [] -> return modules
      newImports -> (((modules <>) . Map.fromList . map assertSuccess) <$>
                     (traverse . traverse) (parseNamedModule oberon2 path) [(p, p) | p <- newImports])
                    >>= parseImportsOf oberon2 path
   where moduleImports = foldMap importsOf modules
         importsOf (Module _ imports _ _ _) = snd <$> imports
         assertSuccess (m, Left err) = error ("Parse error in module " <> unpack m)
         assertSuccess (m, Right [p]) = (m, p)
         assertSuccess (m, Right _) = error ("Ambiguous parses of module " <> unpack m)

-- | Given a directory path for module imports, parse the given module text and all the module files it imports, then
-- use all the information to resolve the syntactic ambiguities.
parseAndResolveModule :: Bool -> Bool -> FilePath -> Text
                      -> IO (Validation (NonEmpty Resolver.Error) (Module Placed Placed))
parseAndResolveModule checkTypes oberon2 path source =
   case parseModule oberon2 source
   of Left err -> return (Failure $ Resolver.UnparseableModule (failureDescription source err 4) :| [])
      Right [rootModule@(Module moduleName imports _ _ _)] ->
         do importedModules <- parseImportsOf oberon2 path (Map.singleton moduleName rootModule)
            let resolvedImportMap = Resolver.resolveModule predefinedScope resolvedImportMap <$> importedModules
                predefinedScope = if oberon2 then Resolver.predefined2 else Resolver.predefined
                successful (Success a) = Just a
                successful _ = Nothing
                typeErrors = TypeChecker.checkModules
                                (if oberon2 then TypeChecker.predefined2 else TypeChecker.predefined)
                                (Map.mapMaybe successful resolvedImportMap)
            when (checkTypes && not (null typeErrors)) (error $ show typeErrors)
            return $ resolvedImportMap Map.! moduleName
      Right _ -> return (Failure $ Resolver.AmbiguousParses :| [])

-- | Parse the module file at the given path, assuming all its imports are in the same directory.
parseAndResolveModuleFile :: Bool -> Bool -> FilePath
                          -> IO (Validation (NonEmpty Resolver.Error) (Module Placed Placed))
parseAndResolveModuleFile checkTypes oberon2 path =
  readFile path >>= parseAndResolveModule checkTypes oberon2 (takeDirectory path)
