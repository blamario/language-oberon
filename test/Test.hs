module Main where

import Data.Either.Validation (Validation(..))
import Data.List (isSuffixOf)
import Data.List.NonEmpty (NonEmpty((:|)))
import Data.Text.IO (readFile)
import Data.Text.Prettyprint.Doc (Pretty(pretty), layoutPretty, defaultLayoutOptions)
import Data.Text.Prettyprint.Doc.Render.Text (renderStrict)
import System.Directory (doesDirectoryExist, listDirectory)
import System.FilePath.Posix (combine)
import Text.Grampa (showFailure)
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.HUnit (assertFailure, assertEqual, testCase)

import Language.Oberon (parseAndResolveModule)
import Language.Oberon.Pretty ()
import qualified Language.Oberon.Resolver as Resolver

import Prelude hiding (readFile)

main = exampleTree "" "examples" >>= defaultMain . testGroup "Oberon"

width = 80
contextLines = 3

exampleTree ancestry path =
   do let fullPath = combine ancestry path
      isDir <- doesDirectoryExist fullPath
      if isDir
         then (:[]) . testGroup path . concat <$> (listDirectory fullPath >>= mapM (exampleTree fullPath))
         else if ".Mod" `isSuffixOf` path
              then return . (:[]) . testCase path $
                   do moduleSource <- readFile fullPath
                      prettyModule <- prettyFile ancestry moduleSource
                      prettyModule' <- prettyFile ancestry prettyModule
                      assertEqual "pretty" prettyModule prettyModule'
              else return []

prettyFile dirPath source = do
   resolvedModule <- parseAndResolveModule True dirPath source
   case resolvedModule
      of Failure (Resolver.UnparseableModule err :| []) -> assertFailure (showFailure source err contextLines)
         Failure errs -> assertFailure (show errs)
         Success mod -> return (renderStrict $ layoutPretty defaultLayoutOptions $ pretty mod)
