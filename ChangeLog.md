# Revision history for language-oberon

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
