# Revision history for language-oberon

## 0.3.4 -- 2025-11-09

* Adjusted for major changes in `deep-transformations` version 0.4

## 0.3.3.2 -- 2025-01-01

* Fixed a few compiler warnings
* Bumped the upper bound of `deep-transformations` and `template-haskell`

## 0.3.3.1 -- 2024-04-27

* Fixed deprecation warnings
* Bumped the upper bound of `filepath`

## 0.3.3  -- 2022-09-26

* Using `OverloadedRecordDot` (GHC >= 9.2) instead of field accessors unsupported by GHC 9.6
* Bumped the upper bounds of `rank2classes`, `transformers`, and `template-haskell`

## 0.3.2  -- 2022-10-23

* Using `autochain` and new imports from grammatical-parsers-0.7

## 0.3.1  -- 2022-10-09

* Incremented the upper bound of the `input-parsers` dependency
* Minor fixes for GHC 9 compatibility

## 0.3  -- 2020-11-01

* Preserving the parsed start and end positions and lexemes of every node
* Added the `Reserializer` module and the `--original` command-line option
* Added the `ConstantFolder` module
* Moved the `Transformation` modules into the new `deep-transformations` package
* Eliminated many of the attribute grammar rules using `Tranformation.AG.Generics`
* Added the `README`

## 0.2.1  -- 2019-01-27

* Pretty-printer fixes
* Testing the idempotence of parse&pretty-print
* Two type parameters for each AST node type, wrapping every field
* Added the Transformation modules
* Added the TypeChecker module

## 0.2  -- 2018-07-09

* Improved error reporting
* Fixed compilation with GHC 8.0.2

## 0.1.1  -- 2018-04-08

* except for the missing Oberon module examples the test suite depends on.

## 0.1  -- 2018-04-08

* First version, but complete enough to be released on an unsuspecting world...
