language-oberon - Oberon parser, pretty-printer, and more
---------------------------------------------------------

This package provides a library and executable for parsing and processing the source code in programming language
Oberon. The following functionality is presently available:

* Parsing with the grammars specified in the
  [Grammar](http://hackage.haskell.org/package/language-oberon/docs/Language-Oberon-Grammar.html) module.
* Resolution of identifiers and disambiguation of a parsed AST with the
  [Resolver](http://hackage.haskell.org/package/language-oberon/docs/Language-Oberon-Resolver.html) module.
* Checking and reporting of type errors with the
  [TypeChecker](http://hackage.haskell.org/package/language-oberon/docs/Language-Oberon-TypeChecker.html) module.
* Constant folding with the
  [ConstantFolder](http://hackage.haskell.org/package/language-oberon/docs/Language-Oberon-ConstantFolder.html) module.
* Re-printing of a parsed AST in its original form, preserving the whitespace and comments, with the
  [Reserializer](http://hackage.haskell.org/package/language-oberon/docs/Language-Oberon-Reserializer.html) module.
* Pretty-printing of a parsed AST with the
  [Pretty](http://hackage.haskell.org/package/language-oberon/docs/Language-Oberon-Pretty.html) module.
