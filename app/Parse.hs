{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Language.Oberon.AST (Module(..))
import qualified Language.Oberon.Grammar as Grammar
import qualified Language.Oberon.Resolver as Resolver

import Control.Monad
import Data.Data (Data)
import Data.Either (fromRight)
import Data.Either.Validation (Validation(..), validationToEither)
import Data.Functor.Identity (Identity)
import Data.Functor.Compose (getCompose)
import Data.List.NonEmpty (NonEmpty)
import qualified Data.Map.Lazy as Map
import Data.Monoid ((<>))
import Data.Text (Text, unpack)
import Data.Text.IO (getLine, readFile)
import Data.Typeable (Typeable)
import Options.Applicative
import Text.Grampa (Ambiguous, Grammar, ParseResults, parseComplete)
import qualified Text.Grampa.ContextFree.LeftRecursive as LeftRecursive
--import Language.Oberon.PrettyPrinter (LPretty(..), displayS, renderPretty)
import ReprTree
import System.FilePath (FilePath, replaceFileName)

import Prelude hiding (getLine, readFile)

data GrammarMode = ModuleWithImportsMode | ModuleMode | AmbiguousModuleMode | DefinitionMode | StatementsMode | StatementMode | ExpressionMode
    deriving Show

data Opts = Opts
    { optsMode        :: GrammarMode
    , optsIndex       :: Int
    , optsPretty      :: Bool
    , optsFile        :: Maybe FilePath
    } deriving Show

main :: IO ()
main = execParser opts >>= main'
  where
    opts = info (helper <*> p)
        ( fullDesc
       <> progDesc "Parse an Oberon file, or parse interactively"
       <> header "Oberon parser")

    p :: Parser Opts
    p = Opts
        <$> (mode <|> pure ModuleWithImportsMode)
        <*> (option auto (long "index" <> help "Index of ambiguous parse" <> showDefault <> value 0 <> metavar "INT"))
        <*> switch
            ( long "pretty"
              <> help "Pretty-print output")
        <*> optional (strArgument
            ( metavar "FILE"
              <> help "Oberon file to parse"))

    mode :: Parser GrammarMode
    mode = ModuleWithImportsMode <$ switch (long "module-with-imports")
       <|> ModuleMode          <$ switch (long "module")
       <|> AmbiguousModuleMode <$ switch (long "module-ambiguous")
       <|> DefinitionMode      <$ switch (long "definition")
       <|> StatementMode       <$ switch (long "statement")
       <|> StatementsMode      <$ switch (long "statements")
       <|> ExpressionMode      <$ switch (long "expression")

main' :: Opts -> IO ()
main' Opts{..} =
    case optsFile of
        Just file -> readFile file
                     >>= case optsMode
                         of ModuleWithImportsMode -> \_-> resolveModuleFile file >>= print
                            ModuleMode          -> go (Resolver.resolveModule mempty) Grammar.module_prod
                                                   Grammar.oberonGrammar file
                            DefinitionMode      -> go (Resolver.resolveModule mempty) Grammar.module_prod
                                                   Grammar.oberonDefinitionGrammar file
                            AmbiguousModuleMode -> go pure Grammar.module_prod Grammar.oberonGrammar file
                            _                   -> error "A file usually contains a whole module."

        Nothing ->
            forever $
            getLine >>=
            case optsMode of
                ModuleMode          -> go (Resolver.resolveModule mempty) Grammar.module_prod
                                          Grammar.oberonGrammar "<stdin>"
                AmbiguousModuleMode -> go pure Grammar.module_prod Grammar.oberonGrammar "<stdin>"
                DefinitionMode      -> go (Resolver.resolveModule mempty) Grammar.module_prod
                                          Grammar.oberonDefinitionGrammar "<stdin>"
                StatementMode       -> go pure Grammar.statement Grammar.oberonGrammar "<stdin>"
                StatementsMode      -> go pure Grammar.statementSequence Grammar.oberonGrammar "<stdin>"
                ExpressionMode      -> go pure Grammar.expression Grammar.oberonGrammar "<stdin>"
  where
    go :: (Show f, Data f) => 
          (f' -> Validation (NonEmpty Resolver.Error) f)
       -> (forall p. Grammar.OberonGrammar Ambiguous p -> p f')
       -> (Grammar (Grammar.OberonGrammar Ambiguous) LeftRecursive.Parser Text)
       -> String -> Text -> IO ()
    go resolve production grammar filename contents =
       case getCompose (production $ parseComplete grammar contents)
       of Right [x] -> succeed (resolve x)
          Right l -> putStrLn ("Ambiguous: " ++ show optsIndex ++ "/" ++ show (length l) ++ " parses") >> succeed (resolve $ l !! optsIndex)
          Left err -> error (show err)
    succeed x = if optsPretty
                then either print (putStrLn . reprTreeString) (validationToEither x)
                else print x

resolveModuleFile :: FilePath -> IO (Validation (NonEmpty Resolver.Error) (Module Identity))
resolveModuleFile path =
   do let parse :: Grammar (Grammar.OberonGrammar Ambiguous) LeftRecursive.Parser Text -> FilePath -> IO (ParseResults ([Module Ambiguous]))
          parse g f = getCompose . Grammar.module_prod . parseComplete g <$> readFile f
      Right [rootModule@(Module _ imports _ _ _)] <- parse Grammar.oberonGrammar path
      importedModules <- (traverse . traverse) (parse Grammar.oberonDefinitionGrammar)
                         [(p, replaceFileName path $ unpack p <> ".Def") | (_, p) <- imports]
      let importMap = Map.fromList $ (head . fromRight undefined <$>) <$> importedModules
      let resolvedImportMap = Resolver.resolveModule resolvedImportMap <$> importMap
      return $ Resolver.resolveModule resolvedImportMap rootModule
