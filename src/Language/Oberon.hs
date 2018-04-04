module Language.Oberon where

import Language.Oberon.AST (Module(..))
import qualified Language.Oberon.Grammar as Grammar
import qualified Language.Oberon.Resolver as Resolver

import Data.Either.Validation (Validation(..))
import Data.Functor.Identity (Identity)
import Data.Functor.Compose (getCompose)
import Data.List.NonEmpty (NonEmpty)
import qualified Data.Map.Lazy as Map
import Data.Map.Lazy (Map)
import Data.Monoid ((<>))
import Data.Text (Text, unpack)
import Data.Text.IO (readFile)
import Text.Grampa (Ambiguous, Grammar, ParseResults, parseComplete)
import qualified Text.Grampa.ContextFree.LeftRecursive as LeftRecursive
import System.Directory (doesFileExist)
import System.FilePath (FilePath, replaceFileName)

import Prelude hiding (readFile)

parseModule :: Bool -> Text -> ParseResults [Module Ambiguous]
parseModule oberon2 = getCompose . Grammar.module_prod
                      . parseComplete (if oberon2 then Grammar.oberon2Grammar else Grammar.oberonGrammar)

parseDefinitionModule :: Bool -> Text -> ParseResults [Module Ambiguous]
parseDefinitionModule oberon2 = getCompose . Grammar.module_prod
                                . parseComplete (if oberon2 then Grammar.oberon2DefinitionGrammar
                                                 else Grammar.oberonDefinitionGrammar)

parseNamedModule :: Bool -> FilePath -> Text -> IO (ParseResults [Module Ambiguous])
parseNamedModule oberon2 path name =
   do let basePath = replaceFileName path (unpack name)
      isDefn <- doesFileExist (basePath <> ".Def")
      let grammar = if oberon2
                    then if isDefn then Grammar.oberon2DefinitionGrammar else Grammar.oberon2Grammar
                    else if isDefn then Grammar.oberonDefinitionGrammar else Grammar.oberonGrammar
      getCompose . Grammar.module_prod . parseComplete grammar
         <$> readFile (basePath <> if isDefn then ".Def" else ".Mod")

parseImportsOf :: Bool -> FilePath -> Map Text (Module Ambiguous) -> IO (Map Text (Module Ambiguous))
parseImportsOf oberon2 path modules =
   case filter (`Map.notMember` modules) moduleImports
   of [] -> return modules
      newImports -> (((modules <>) . Map.fromList . map assertSuccess) <$>
                     (traverse . traverse) (parseNamedModule oberon2 path) [(p, p) | p <- newImports])
                    >>= parseImportsOf oberon2 path
   where moduleImports = foldMap importsOf modules
         importsOf (Module _ imports _ _ _) = snd <$> imports
         assertSuccess (m, Left err) = error ("Parse error in module " <> unpack m <> ":" <> show err)
         assertSuccess (m, Right [p]) = (m, p)
         assertSuccess (m, Right _) = error ("Ambiguous parses of module " <> unpack m)

parseAndResolveModuleFile :: Bool -> FilePath -> IO (Validation (NonEmpty Resolver.Error) (Module Identity))
parseAndResolveModuleFile oberon2 path =
   do Right [rootModule@(Module moduleName imports _ _ _)] <- parseModule oberon2 <$> readFile path
      importedModules <- parseImportsOf oberon2 path (Map.singleton moduleName rootModule)
      let resolvedImportMap = Resolver.resolveModule predefinedScope resolvedImportMap <$> importedModules
          predefinedScope = if oberon2 then Resolver.predefined2 else Resolver.predefined
      return $ Resolver.resolveModule predefinedScope resolvedImportMap rootModule
