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
import System.FilePath (FilePath, replaceFileName)

import Prelude hiding (readFile)

parseModule :: Text -> ParseResults [Module Ambiguous]
parseModule = getCompose . Grammar.module_prod . parseComplete Grammar.oberonGrammar

parseDefinitionModule :: Text -> ParseResults [Module Ambiguous]
parseDefinitionModule = getCompose . Grammar.module_prod . parseComplete Grammar.oberonDefinitionGrammar

parseAndResolveModuleFile :: FilePath -> IO (Validation (NonEmpty Resolver.Error) (Module Identity))
parseAndResolveModuleFile path =
   do Right [rootModule@(Module _ imports _ _ _)] <- parseModule <$> readFile path
      importedModules <- (traverse . traverse) ((parseDefinitionModule <$>) . readFile)
                         [(p, replaceFileName path $ unpack p <> ".Def") | (_, p) <- imports]
      let importMap = Map.fromList (assertSuccess <$> importedModules)
          assertSuccess (m, Left err) = error ("Parse error in module " <> unpack m <> ":" <> show err)
          assertSuccess (m, Right [p]) = (m, p)
          assertSuccess (m, Right _) = error ("Ambiguos parses of module " <> unpack m)
          resolvedImportMap = Resolver.resolveModule resolvedImportMap <$> importMap
      return $ Resolver.resolveModule resolvedImportMap rootModule
