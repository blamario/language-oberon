{-# LANGUAGE FlexibleContexts, FlexibleInstances, RankNTypes, RecordWildCards, ScopedTypeVariables, TypeFamilies #-}

module Main where

import Language.Oberon (Placed, LanguageVersion(Oberon1, Oberon2), parseAndResolveModule, resolvePosition, resolvePositions)
import Language.Oberon.AST (Module(..), StatementSequence, Statement, Expression)
import qualified Language.Oberon.Grammar as Grammar
import qualified Language.Oberon.Resolver as Resolver
import qualified Language.Oberon.TypeChecker as TypeChecker
import qualified Language.Oberon.Pretty ()

import qualified Transformation.Rank2 as Rank2
import qualified Transformation.Deep as Deep

import Data.Text.Prettyprint.Doc (Pretty(pretty))
import Data.Text.Prettyprint.Doc.Util (putDocW)

import Control.Monad
import Data.Data (Data)
import Data.Either.Validation (Validation(..), validationToEither)
import Data.Functor.Identity (Identity(Identity))
import Data.Functor.Compose (Compose, getCompose)
import Data.List.NonEmpty (NonEmpty((:|)))
import qualified Data.Map.Lazy as Map
import Data.Maybe (fromMaybe)
import Data.Monoid ((<>))
import Data.Text (Text, unpack)
import Data.Text.IO (getLine, readFile, getContents)
import qualified Data.Text.IO as Text
import Data.Typeable (Typeable)
import Options.Applicative
import Text.Grampa (Ambiguous, Grammar, ParseResults, parseComplete, failureDescription, offsetContext)
import qualified Text.Grampa.ContextFree.LeftRecursive as LeftRecursive
import ReprTree
import System.FilePath (FilePath, addExtension, combine, takeDirectory)

import Prelude hiding (getLine, getContents, readFile)

data GrammarMode = TypeCheckedModuleMode | ModuleWithImportsMode | ModuleMode | AmbiguousModuleMode | DefinitionMode
                 | StatementsMode | StatementMode | ExpressionMode
    deriving Show

data Output = Plain | Pretty Int | Tree
            deriving Show

data Opts = Opts
    { optsMode        :: GrammarMode
    , optsVersion     :: LanguageVersion
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
        <$> mode
        <*> (Oberon2 <$ switch (long "oberon2")
             <|> Oberon1 <$ switch (long "oberon1")
             <|> pure Oberon1)
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
    mode = TypeCheckedModuleMode <$ switch (long "type-checked-module")
       <|> ModuleWithImportsMode <$ switch (long "module-with-imports")
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
                         of TypeCheckedModuleMode ->
                               let dir = fromMaybe (takeDirectory file) optsInclude
                               in \source-> parseAndResolveModule True optsVersion dir source
                                            >>= succeed optsOutput (reportTypeErrorIn dir) id
                            ModuleWithImportsMode ->
                              \source-> parseAndResolveModule False optsVersion
                                          (fromMaybe (takeDirectory file) optsInclude) source
                                        >>= succeed optsOutput (error "no type checking") id
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
                ModuleMode          -> go (Resolver.resolveModule predefined mempty) Grammar.module_prod
                                          chosenGrammar "<stdin>"
                AmbiguousModuleMode -> go pure Grammar.module_prod chosenGrammar "<stdin>"
                DefinitionMode      -> go (Resolver.resolveModule predefined mempty) Grammar.module_prod
                                          Grammar.oberonDefinitionGrammar "<stdin>"
                StatementMode       -> go pure Grammar.statement chosenGrammar "<stdin>"
                StatementsMode      -> go pure Grammar.statementSequence chosenGrammar "<stdin>"
                ExpressionMode      -> \src-> case getCompose ((resolvePosition src . (resolvePositions src <$>))
                                                               <$> Grammar.expression (parseComplete chosenGrammar src))
                                              of Right [x] -> succeed optsOutput (error "no type checking") 
                                                                      Left (pure x)
                                                 Right l -> putStrLn ("Ambiguous: " ++ show optsIndex ++ "/"
                                                                      ++ show (length l) ++ " parses")
                                                            >> succeed optsOutput (error "no type checking") 
                                                                       Left (pure $ l !! optsIndex)
                                                 Left err -> Text.putStrLn (failureDescription src err 4)
  where
    chosenGrammar = case optsVersion 
                    of Oberon1 -> Grammar.oberonGrammar
                       Oberon2 -> Grammar.oberon2Grammar 
    predefined = case optsVersion 
                 of Oberon1 -> Resolver.predefined
                    Oberon2 -> Resolver.predefined2
    go :: (Show a, Data a, Pretty a, a ~ t f f,
           Deep.Functor (Rank2.Map Grammar.NodeWrap NodeWrap) t Grammar.NodeWrap NodeWrap) =>
          (t NodeWrap NodeWrap -> Validation (NonEmpty Resolver.Error) a)
       -> (forall p. Grammar.OberonGrammar Grammar.NodeWrap p -> p (t Grammar.NodeWrap Grammar.NodeWrap))
       -> (Grammar (Grammar.OberonGrammar Grammar.NodeWrap) LeftRecursive.Parser Text)
       -> String -> Text -> IO ()
    go resolve production grammar filename contents =
       case getCompose (resolvePositions contents <$> production (parseComplete grammar contents))
       of Right [x] -> succeed optsOutput (reportTypeErrorIn $ takeDirectory filename) Left (resolve x)
          Right l -> putStrLn ("Ambiguous: " ++ show optsIndex ++ "/" ++ show (length l) ++ " parses")
                     >> succeed optsOutput (reportTypeErrorIn $ takeDirectory filename) Left (resolve $ l !! optsIndex)
          Left err -> Text.putStrLn (failureDescription contents err 4)

type NodeWrap = Compose ((,) Int) Ambiguous

succeed :: (Data a, Pretty a, Show a) 
        => Output -> (TypeChecker.Error -> IO ()) -> (err -> Either (NonEmpty Resolver.Error) (NonEmpty TypeChecker.Error)) 
           -> Validation err a -> IO ()
succeed out reportTypeError prepare x = either (reportFailure . prepare) showSuccess (validationToEither x)
   where reportFailure (Left (Resolver.UnparseableModule err :| [])) = Text.putStrLn err
         reportFailure (Left errs) = print errs
         reportFailure (Right errs) = mapM_ reportTypeError errs
         showSuccess = case out
                       of Pretty width -> putDocW width . pretty
                          Tree -> putStrLn . reprTreeString
                          Plain -> print

reportTypeErrorIn directory (moduleName, pos, err) =
   do contents <- readFile (combine directory $ addExtension (unpack moduleName) "Mod")
      putStrLn ("Type error: " ++ TypeChecker.errorMessage err)
      Text.putStrLn (offsetContext contents pos 4)

instance Pretty (Module Placed Placed) where
   pretty m = pretty ((Identity . snd) Rank2.<$> m)
instance Pretty (Module NodeWrap NodeWrap) where
   pretty _ = error "Disambiguate before pretty-printing"
instance Pretty (StatementSequence NodeWrap NodeWrap) where
   pretty _ = error "Disambiguate before pretty-printing"
instance Pretty (NodeWrap (Statement NodeWrap NodeWrap)) where
   pretty _ = error "Disambiguate before pretty-printing"
instance Pretty (Statement NodeWrap NodeWrap) where
   pretty _ = error "Disambiguate before pretty-printing"
instance Pretty (Expression NodeWrap NodeWrap) where
   pretty _ = error "Disambiguate before pretty-printing"
instance Pretty (NodeWrap (Expression NodeWrap NodeWrap)) where
   pretty _ = error "Disambiguate before pretty-printing"
