module Main where

import Data.Either.Validation (Validation(..))
import Data.List (isSuffixOf)
import System.Directory (doesDirectoryExist, listDirectory)
import System.FilePath.Posix (combine)
import Test.Tasty (TestTree, defaultMain, testGroup)
import Test.Tasty.HUnit (assertFailure, testCase)

import Language.Oberon (parseAndResolveModuleFile)

main = exampleTree "" "examples" >>= defaultMain . testGroup "Oberon"

exampleTree ancestry path =
   do let fullPath = combine ancestry path
      isDir <- doesDirectoryExist fullPath
      if isDir
         then (:[]) . testGroup path . concat <$> (listDirectory fullPath >>= mapM (exampleTree fullPath))
         else if ".Mod" `isSuffixOf` path
              then return . (:[]) . testCase path $
                   do resolvedModule <- parseAndResolveModuleFile True fullPath
                      case resolvedModule
                           of Failure err -> assertFailure (show err)
                              Success{} -> pure ()
              else return []
