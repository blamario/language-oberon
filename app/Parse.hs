{-# LANGUAGE FlexibleContexts, FlexibleInstances, RankNTypes, RecordWildCards, ScopedTypeVariables, TypeFamilies #-}

module Main where

import Language.Oberon (Placed, LanguageVersion(Oberon1, Oberon2), Options(..),
                        parseAndResolveModule, resolvePosition, resolvePositions)
import Language.Oberon.AST (Language, Module(..), StatementSequence, Statement, Expression)
import qualified Language.Oberon.AST as AST
import qualified Language.Oberon.Grammar as Grammar
import qualified Language.Oberon.Resolver as Resolver
import qualified Language.Oberon.TypeChecker as TypeChecker
import qualified Language.Oberon.Pretty ()

import qualified Transformation.Rank2 as Rank2
import qualified Transformation.Deep as Deep

import Data.Text.Prettyprint.Doc (Pretty(pretty))
import Data.Text.Prettyprint.Doc.Util (putDocW)

import Control.Arrow (second)
import Control.Monad
import Data.Data (Data)
import Data.Either.Validation (Validation(..), validationToEither)
import Data.Functor.Identity (Identity(Identity))
import Data.Functor.Compose (Compose(..))
import Data.List.NonEmpty (NonEmpty((:|)))
import Data.Maybe (fromMaybe)
import Data.Monoid ((<>))
import Data.Text (Text, unpack)
import Data.Text.IO (getLine, readFile, getContents)
import qualified Data.Text.IO as Text
import Options.Applicative
import Text.Grampa (Ambiguous, Grammar, parseComplete, failureDescription, offsetContext)
import qualified Text.Grampa.ContextFree.LeftRecursive as LeftRecursive
import ReprTree
import System.FilePath (FilePath, addExtension, combine, takeDirectory)

import Prelude hiding (getLine, getContents, readFile)

data GrammarMode = ModuleWithImportsMode | ModuleMode | AmbiguousModuleMode | DefinitionMode
                 | StatementMode | ExpressionMode
    deriving Show

data Output = Plain | Pretty Int | Tree
            deriving Show

data Opts = Opts
    { optsMode          :: GrammarMode
    , optsVersion       :: LanguageVersion
    , optsCheckTypes    :: Bool
    , optsFoldConstants :: Bool
    , optsIndex         :: Int
    , optsOutput        :: Output
    , optsInclude       :: Maybe FilePath
    , optsFile          :: Maybe FilePath
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
        <$> mode
        <*> (flag' Oberon2 (long "oberon2")
             <|> flag' Oberon1 (long "oberon1")
             <|> pure Oberon2)
        <*> (switch (long "check-types"))
        <*> (switch (long "fold-constants"))
        <*> (option auto (long "index" <> help "Index of ambiguous parse" <> showDefault <> value 0 <> metavar "INT"))
        <*> (Pretty <$> option auto (long "pretty" <> help "Pretty-print output" <> metavar "WIDTH")
             <|> flag' Tree (long "tree" <> help "Print the output as an abstract syntax tree")
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
                               let dir = fromMaybe (takeDirectory file) optsInclude
                               in \source-> parseAndResolveModule Options{checkTypes= optsCheckTypes,
                                                                          foldConstants= optsFoldConstants,
                                                                          version= optsVersion} dir source
                                            >>= succeed optsOutput (reportTypeErrorIn dir) id
                            ModuleMode ->
                              go (Resolver.resolveModule predefined mempty) Grammar.module_prod chosenGrammar file
                            DefinitionMode ->
                              go (Resolver.resolveModule predefined mempty) Grammar.module_prod
                                 Grammar.oberonDefinitionGrammar file
                            AmbiguousModuleMode ->
                              go pure Grammar.module_prod chosenGrammar file
                            _ -> error "A file usually contains a whole module."

        Nothing ->
            forever $
            getLine >>=
            case optsMode of
                ModuleWithImportsMode ->
                    let dir = fromMaybe "." optsInclude
                    in \source-> parseAndResolveModule Options{checkTypes= optsCheckTypes,
                                                               foldConstants= optsFoldConstants,
                                                               version= optsVersion} dir source
                                 >>= succeed optsOutput (reportTypeErrorIn dir) id
                ModuleMode          -> go (Resolver.resolveModule predefined mempty) Grammar.module_prod
                                          chosenGrammar "<stdin>"
                AmbiguousModuleMode -> go pure Grammar.module_prod chosenGrammar "<stdin>"
                DefinitionMode      -> go (Resolver.resolveModule predefined mempty) Grammar.module_prod
                                          Grammar.oberonDefinitionGrammar "<stdin>"
                StatementMode       -> go pure Grammar.statement chosenGrammar "<stdin>"
                ExpressionMode      -> go pure Grammar.expression chosenGrammar "<stdin>"

  where
    chosenGrammar = case optsVersion 
                    of Oberon1 -> Grammar.oberonGrammar
                       Oberon2 -> Grammar.oberon2Grammar 
    predefined = case optsVersion 
                 of Oberon1 -> Resolver.predefined
                    Oberon2 -> Resolver.predefined2
    go :: (Show a, Data a, Pretty a, a ~ f (g f f),
           Deep.Functor (Rank2.Map Grammar.NodeWrap NodeWrap) g) =>
          (NodeWrap (g NodeWrap NodeWrap) -> Validation (NonEmpty (Resolver.Error Language)) a)
       -> (forall p. Grammar.OberonGrammar AST.Language Grammar.NodeWrap p
                  -> p (Grammar.NodeWrap (g Grammar.NodeWrap Grammar.NodeWrap)))
       -> (Grammar (Grammar.OberonGrammar AST.Language Grammar.NodeWrap) Grammar.Parser Text)
       -> String -> Text -> IO ()
    go resolve production grammar filename contents =
       case getCompose (second (resolvePositions contents) <$> getCompose (production $ parseComplete grammar contents))
       of Right [(s, x)] -> succeed optsOutput (reportTypeErrorIn $ takeDirectory filename) Left (resolve x)
          Right l -> putStrLn ("Ambiguous: " ++ show optsIndex ++ "/" ++ show (length l) ++ " parses")
                     >> succeed optsOutput (reportTypeErrorIn $ takeDirectory filename) Left (resolve . snd $ l !! optsIndex)
          Left err -> Text.putStrLn (failureDescription contents err 4)

type NodeWrap = Compose ((,) Int) (Compose Ambiguous ((,) Grammar.ParsedLexemes))

succeed :: (Data a, Pretty a, Show a)
        => Output -> (TypeChecker.Error Language -> IO ())
        -> (err -> Either (NonEmpty (Resolver.Error Language)) (NonEmpty (TypeChecker.Error Language)))
        -> Validation err a -> IO ()
succeed out reportTypeError prepare x = either (reportFailure . prepare) showSuccess (validationToEither x)
   where reportFailure (Left (Resolver.UnparseableModule err :| [])) = Text.putStrLn err
         reportFailure (Left errs) = print errs
         reportFailure (Right errs) = mapM_ reportTypeError errs
         showSuccess = case out
                       of Pretty width -> putDocW width . pretty
                          Tree -> putStrLn . reprTreeString
                          Plain -> print

reportTypeErrorIn directory (moduleName, (pos, _), err) =
   do contents <- readFile (combine directory $ addExtension (unpack moduleName) "Mod")
      putStrLn ("Type error: " ++ TypeChecker.errorMessage err)
      Text.putStrLn (offsetContext contents pos 4)

instance {-# overlaps #-} Pretty a => Pretty (Placed a) where
   pretty = pretty . snd
instance Pretty (Module Language Language Placed Placed) where
   pretty m = pretty ((Identity . snd) Rank2.<$> m)
instance Pretty (Module Language Language NodeWrap NodeWrap) where
   pretty _ = error "Disambiguate before pretty-printing"
instance Pretty (StatementSequence Language Language NodeWrap NodeWrap) where
   pretty _ = error "Disambiguate before pretty-printing"
instance Pretty (Statement Language Language NodeWrap NodeWrap) where
   pretty _ = error "Disambiguate before pretty-printing"
instance Pretty (Expression Language Language NodeWrap NodeWrap) where
   pretty _ = error "Disambiguate before pretty-printing"
instance Pretty (NodeWrap a) where
   pretty _ = error "Disambiguate before pretty-printing"
