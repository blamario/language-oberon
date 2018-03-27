{-# LANGUAGE FlexibleInstances, RankNTypes, RecordWildCards, ScopedTypeVariables #-}

module Main where

import Language.Oberon (parseAndResolveModuleFile)
import Language.Oberon.AST (Module(..), Statement, Expression)
import qualified Language.Oberon.Grammar as Grammar
import qualified Language.Oberon.Resolver as Resolver
import qualified Language.Oberon.Pretty ()
import Data.Text.Prettyprint.Doc (Pretty(pretty))
import Data.Text.Prettyprint.Doc.Util (putDocW)

import Control.Monad
import Data.Data (Data)
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
import ReprTree
import System.FilePath (FilePath)

import Prelude hiding (getLine, readFile)

data GrammarMode = ModuleWithImportsMode | ModuleMode | AmbiguousModuleMode | DefinitionMode | StatementsMode | StatementMode | ExpressionMode
    deriving Show

data Output = Plain | Pretty Int | Tree
            deriving Show

data Opts = Opts
    { optsMode        :: GrammarMode
    , optsOberon2     :: Bool
    , optsIndex       :: Int
    , optsOutput      :: Output
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
        <*> (switch (long "oberon2"))
        <*> (option auto (long "index" <> help "Index of ambiguous parse" <> showDefault <> value 0 <> metavar "INT"))
        <*> (Pretty <$> option auto (long "pretty" <> help "Pretty-print output" <> metavar "WIDTH")
             <|> Tree <$ switch (long "tree" <> help "Print the output as an abstract syntax tree")
             <|> pure Plain)
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
                         of ModuleWithImportsMode -> \_-> parseAndResolveModuleFile file >>= succeed optsOutput
                            ModuleMode          -> go (Resolver.resolveModule mempty) Grammar.module_prod
                                                   chosenGrammar file
                            DefinitionMode      -> go (Resolver.resolveModule mempty) Grammar.module_prod
                                                   Grammar.oberonDefinitionGrammar file
                            AmbiguousModuleMode -> go pure Grammar.module_prod chosenGrammar file
                            _                   -> error "A file usually contains a whole module."

        Nothing ->
            forever $
            getLine >>=
            case optsMode of
                ModuleMode          -> go (Resolver.resolveModule mempty) Grammar.module_prod
                                          chosenGrammar "<stdin>"
                AmbiguousModuleMode -> go pure Grammar.module_prod chosenGrammar "<stdin>"
                DefinitionMode      -> go (Resolver.resolveModule mempty) Grammar.module_prod
                                          Grammar.oberonDefinitionGrammar "<stdin>"
                StatementMode       -> go pure Grammar.statement chosenGrammar "<stdin>"
                StatementsMode      -> go pure Grammar.statementSequence chosenGrammar "<stdin>"
                ExpressionMode      -> go pure Grammar.expression chosenGrammar "<stdin>"
  where
    chosenGrammar = if optsOberon2 then Grammar.oberon2Grammar else Grammar.oberonGrammar
    go :: (Show f, Data f, Pretty f) => 
          (f' -> Validation (NonEmpty Resolver.Error) f)
       -> (forall p. Grammar.OberonGrammar Ambiguous p -> p f')
       -> (Grammar (Grammar.OberonGrammar Ambiguous) LeftRecursive.Parser Text)
       -> String -> Text -> IO ()
    go resolve production grammar filename contents =
       case getCompose (production $ parseComplete grammar contents)
       of Right [x] -> succeed optsOutput (resolve x)
          Right l -> putStrLn ("Ambiguous: " ++ show optsIndex ++ "/" ++ show (length l) ++ " parses")
                     >> succeed optsOutput (resolve $ l !! optsIndex)
          Left err -> error (show err)

succeed out x = case out
                of Pretty width -> either print (putDocW width . pretty) (validationToEither x)
                   Tree -> either print (putStrLn . reprTreeString) (validationToEither x)
                   Plain -> print x

instance Pretty (Module Ambiguous) where
   pretty _ = error "Disambiguate before pretty-printing"
instance Pretty (Ambiguous (Statement Ambiguous)) where
   pretty _ = error "Disambiguate before pretty-printing"
instance Pretty (Statement Ambiguous) where
   pretty _ = error "Disambiguate before pretty-printing"
instance Pretty (Expression Ambiguous) where
   pretty _ = error "Disambiguate before pretty-printing"
