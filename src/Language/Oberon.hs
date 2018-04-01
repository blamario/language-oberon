module Language.Oberon where

import Language.Oberon.AST (Module(..))
import qualified Language.Oberon.Grammar as Grammar
import qualified Language.Oberon.Resolver as Resolver

import Data.Either.Validation (Validation(..))
import Data.Functor.Identity (Identity)
import Data.Functor.Compose (getCompose)
import Data.List.NonEmpty (NonEmpty)
import qualified Data.Map.Lazy as Map
import Data.Monoid ((<>))
import Data.Text (Text, unpack)
import Data.Text.IO (readFile)
import Text.Grampa (Ambiguous, Grammar, ParseResults, parseComplete)
import qualified Text.Grampa.ContextFree.LeftRecursive as LeftRecursive
import System.Directory (doesFileExist)
import System.FilePath (FilePath, replaceFileName)

import Prelude hiding (readFile)

parseModule :: Text -> ParseResults [Module Ambiguous]
parseModule = getCompose . Grammar.module_prod . parseComplete Grammar.oberonGrammar

parseDefinitionModule :: Text -> ParseResults [Module Ambiguous]
parseDefinitionModule = getCompose . Grammar.module_prod . parseComplete Grammar.oberonDefinitionGrammar

parseAndResolveModuleFile :: Bool -> FilePath -> IO (Validation (NonEmpty Resolver.Error) (Module Identity))
parseAndResolveModuleFile oberon2 path =
   do Right [rootModule@(Module _ imports _ _ _)] <- parseModule <$> readFile path
      let readAvailableFile name = do isDefn <- doesFileExist (name <> ".Def")
                                      readFile (name <> if isDefn then ".Def" else ".Mod")
      importedModules <- (traverse . traverse) ((parseDefinitionModule <$>) . readAvailableFile)
                         [(p, replaceFileName path $ unpack p) | (_, p) <- imports]
      let importMap = Map.fromList (assertSuccess <$> importedModules)
          assertSuccess (m, Left err) = error ("Parse error in module " <> unpack m <> ":" <> show err)
          assertSuccess (m, Right [p]) = (m, p)
          assertSuccess (m, Right _) = error ("Ambiguous parses of module " <> unpack m)
          resolvedImportMap = Resolver.resolveModule predefinedScope resolvedImportMap <$> importMap
          predefinedScope = if oberon2 then Resolver.predefined2 else Resolver.predefined
      return $ Resolver.resolveModule predefinedScope resolvedImportMap rootModule
