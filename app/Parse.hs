{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import qualified Language.Oberon.Grammar as Grammar
import qualified Language.Oberon.Resolver as Resolver

import Control.Monad
import Data.Data (Data)
import Data.Either.Validation (Validation(..), validationToEither)
import Data.Functor.Compose (getCompose)
import Data.List.NonEmpty (NonEmpty)
import Data.Monoid ((<>))
import Data.Text (Text)
import Data.Text.IO (getLine, readFile)
import Data.Typeable (Typeable)
import Options.Applicative
import Text.Grampa (Ambiguous, parseComplete)
--import Language.Oberon.PrettyPrinter (LPretty(..), displayS, renderPretty)
import ReprTree

import Prelude hiding (getLine, readFile)

data GrammarMode = ModuleMode | AmbiguousModuleMode | StatementsMode | StatementMode | ExpressionMode
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
        <$> (mode <|> pure ExpressionMode)
        <*> (option auto (long "index" <> help "Index of ambiguous parse" <> showDefault <> value 0 <> metavar "INT"))
        <*> switch
            ( long "pretty"
              <> help "Pretty-print output")
        <*> optional (strArgument
            ( metavar "FILE"
              <> help "Oberon file to parse"))

    mode :: Parser GrammarMode
    mode = ModuleMode          <$ switch (long "module")
       <|> AmbiguousModuleMode <$ switch (long "module-ambiguous")
       <|> StatementMode       <$ switch (long "statement")
       <|> StatementsMode      <$ switch (long "statements")
       <|> ExpressionMode      <$ switch (long "expression")

main' :: Opts -> IO ()
main' Opts{..} =
    case optsFile of
        Just file -> readFile file >>= go (Resolver.resolveModule mempty) Grammar.module_prod file
        Nothing ->
            case optsMode of
                ModuleMode          -> forever $ 
                                       getLine >>= go (Resolver.resolveModule mempty) Grammar.module_prod "<stdin>"
                AmbiguousModuleMode -> forever $ getLine >>= go pure Grammar.module_prod "<stdin>"
                StatementMode       -> forever $ getLine >>= go pure Grammar.statement "<stdin>"
                StatementsMode      -> forever $ getLine >>= go pure Grammar.statementSequence "<stdin>"
                ExpressionMode      -> forever $ getLine >>= go pure Grammar.expression "<stdin>"
  where
    go :: (Show f, Data f) => 
          (f' -> Validation (NonEmpty Resolver.Error) f) -> (forall p. Grammar.OberonGrammar Ambiguous p -> p f') -> String -> Text -> IO ()
    go resolve f filename contents = case getCompose (f $ parseComplete Grammar.oberonGrammar contents)
                                     of Right [x] -> succeed (resolve x)
                                        Right l -> putStrLn ("Ambiguous: " ++ show optsIndex ++ "/" ++ show (length l) ++ " parses") >> succeed (resolve $ l !! optsIndex)
                                        Left err -> error (show err)
    succeed x = if optsPretty
                then either print (putStrLn . reprTreeString) (validationToEither x)
                else print x
