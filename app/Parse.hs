{-# LANGUAGE FlexibleInstances, RankNTypes, RecordWildCards, ScopedTypeVariables #-}

module Main where

import Language.Oberon (parseAndResolveModule)
import Language.Oberon.AST (Module(..), StatementSequence, Statement, Expression)
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
import Data.List.NonEmpty (NonEmpty((:|)))
import qualified Data.Map.Lazy as Map
import Data.Maybe (fromMaybe)
import Data.Monoid ((<>))
import Data.Text (Text, unpack)
import Data.Text.IO (getLine, readFile, getContents)
import Data.Typeable (Typeable)
import Options.Applicative
import Text.Grampa (Ambiguous, Grammar, ParseResults, parseComplete, showFailure)
import qualified Text.Grampa.ContextFree.LeftRecursive as LeftRecursive
import ReprTree
import System.FilePath (FilePath, takeDirectory)

import Prelude hiding (getLine, getContents, readFile)

data GrammarMode = ModuleWithImportsMode | ModuleMode | AmbiguousModuleMode | DefinitionMode | StatementsMode | StatementMode | ExpressionMode
    deriving Show

data Output = Plain | Pretty Int | Tree
            deriving Show

data Opts = Opts
    { optsMode        :: GrammarMode
    , optsOberon2     :: Bool
    , optsIndex       :: Int
    , optsOutput      :: Output
    , optsInclude     :: Maybe FilePath
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
        <*> optional (strOption (short 'i' <> long "include" <> metavar "DIRECTORY"
                                 <> help "Where to look for imports"))
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
        Just file -> (if file == "-" then getContents else readFile file)
                     >>= case optsMode
                         of ModuleWithImportsMode ->
                               \source-> parseAndResolveModule optsOberon2
                                                               (fromMaybe (takeDirectory file) optsInclude) source
                                         >>= succeed optsOutput source
                            ModuleMode          -> go (Resolver.resolveModule predefined mempty) Grammar.module_prod
                                                   chosenGrammar file
                            DefinitionMode      -> go (Resolver.resolveModule predefined mempty) Grammar.module_prod
                                                   Grammar.oberonDefinitionGrammar file
                            AmbiguousModuleMode -> go pure Grammar.module_prod chosenGrammar file
                            _                   -> error "A file usually contains a whole module."

        Nothing ->
            forever $
            getLine >>=
            case optsMode of
                ModuleMode          -> go (Resolver.resolveModule predefined mempty) Grammar.module_prod
                                          chosenGrammar "<stdin>"
                AmbiguousModuleMode -> go pure Grammar.module_prod chosenGrammar "<stdin>"
                DefinitionMode      -> go (Resolver.resolveModule predefined mempty) Grammar.module_prod
                                          Grammar.oberonDefinitionGrammar "<stdin>"
                StatementMode       -> go pure Grammar.statement chosenGrammar "<stdin>"
                StatementsMode      -> go pure Grammar.statementSequence chosenGrammar "<stdin>"
                ExpressionMode      -> go pure Grammar.expression chosenGrammar "<stdin>"
  where
    chosenGrammar = if optsOberon2 then Grammar.oberon2Grammar else Grammar.oberonGrammar
    predefined = if optsOberon2 then Resolver.predefined2 else Resolver.predefined
    go :: (Show f, Data f, Pretty f) => 
          (f' -> Validation (NonEmpty Resolver.Error) f)
       -> (forall p. Grammar.OberonGrammar Ambiguous p -> p f')
       -> (Grammar (Grammar.OberonGrammar Ambiguous) LeftRecursive.Parser Text)
       -> String -> Text -> IO ()
    go resolve production grammar filename contents =
       case getCompose (production $ parseComplete grammar contents)
       of Right [x] -> succeed optsOutput contents (resolve x)
          Right l -> putStrLn ("Ambiguous: " ++ show optsIndex ++ "/" ++ show (length l) ++ " parses")
                     >> succeed optsOutput contents (resolve $ l !! optsIndex)
          Left err -> putStrLn (showFailure contents err 3)

succeed out contents x = either reportFailure showSuccess (validationToEither x)
   where reportFailure (Resolver.UnparseableModule err :| []) = putStrLn (showFailure contents err 3)
         reportFailure errs = print errs
         showSuccess = case out
                       of Pretty width -> putDocW width . pretty
                          Tree -> putStrLn . reprTreeString
                          Plain -> print

instance Pretty (Module Ambiguous Ambiguous) where
   pretty _ = error "Disambiguate before pretty-printing"
instance Pretty (StatementSequence Ambiguous Ambiguous) where
   pretty _ = error "Disambiguate before pretty-printing"
instance Pretty (Ambiguous (Statement Ambiguous Ambiguous)) where
   pretty _ = error "Disambiguate before pretty-printing"
instance Pretty (Statement Ambiguous Ambiguous) where
   pretty _ = error "Disambiguate before pretty-printing"
instance Pretty (Expression Ambiguous Ambiguous) where
   pretty _ = error "Disambiguate before pretty-printing"
