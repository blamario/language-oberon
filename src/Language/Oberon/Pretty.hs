{-# LANGUAGE FlexibleInstances, OverloadedStrings #-}

module Language.Oberon.Pretty where

import Data.Functor.Identity (Identity(..))
import Data.List.NonEmpty (NonEmpty((:|)), fromList, toList)
import Data.Text.Prettyprint.Doc
import Numeric (showHex)

import Language.Oberon.AST

instance Pretty (Module Identity) where
   pretty (Module name imports declarations body name') =
      vsep ["MODULE" <+> pretty name <> ";",
            if null imports then mempty
            else "IMPORT" <+> align (vsep (punctuate comma $ prettyImport <$> imports)) <> semi,
            vsep (pretty <$> declarations),
            maybe mempty (\statements-> vsep ["BEGIN", prettyBlock statements]) body,
            "END" <+> pretty name' <> "."]
      where prettyImport (Nothing, mod) = pretty mod
            prettyImport (Just inner, mod) = pretty inner <> ":=" <+> pretty mod

instance Pretty (Declaration Identity) where
   pretty (ConstantDeclaration ident expr) = "CONST" <+> pretty ident <+> "=" <+> pretty expr <> semi
   pretty (TypeDeclaration ident typeDef) = "TYPE" <+> pretty ident <+> "=" <+> pretty typeDef <> semi
   pretty (VariableDeclaration idents varType) =
      "VAR" <+> hsep (punctuate comma $ pretty <$> toList idents) <+> colon <+> pretty varType
   pretty (ProcedureDeclaration heading body name) = vsep [pretty heading <> semi,
                                                           pretty body,
                                                           "END" <+> pretty name]
   pretty (ForwardDeclaration ident parameters) = "PROCEDURE" <+> "^" <+> pretty ident <+> pretty parameters

instance Pretty IdentDef where
   pretty (IdentDef name True) = pretty name <> "*"
   pretty (IdentDef name False) = pretty name

instance Pretty (Expression Identity) where
   pretty = prettyPrec 0
      where prettyPrec 0 (Relation op left right) = prettyPrec 1 left <+> pretty op <+> prettyPrec 1 right
            prettyPrec p (Positive e) | p < 2 = "+" <> prettyPrec 2 e
            prettyPrec p (Negative e) | p < 2 = "-" <> prettyPrec 2 e
            prettyPrec p (Add left right) | p < 3 = prettyPrec 3 left <> "+" <> prettyPrec 3 right
            prettyPrec p (Subtract left right) | p < 3 = prettyPrec 3 left <> "-" <> prettyPrec 3 right
            prettyPrec p (Or left right) | p < 3 = prettyPrec 3 left <+> "OR" <+> prettyPrec 3 right
            prettyPrec p (Multiply left right) | p < 4 = prettyPrec 4 left <> "*" <> prettyPrec 4 right
            prettyPrec p (Divide left right) | p < 4 = prettyPrec 4 left <> "/" <> prettyPrec 4 right
            prettyPrec p (IntegerDivide left right) | p < 4 = prettyPrec 4 left <+> "DIV" <+> prettyPrec 4 right
            prettyPrec p (Modulo left right) | p < 4 = prettyPrec 4 left <+> "MOD" <+> prettyPrec 4 right
            prettyPrec p (And left right) | p < 4 = prettyPrec 4 left <+> "&" <+> prettyPrec 4 right
            prettyPrec _ (Integer n) = pretty n
            prettyPrec _ (Real r) = pretty r
            prettyPrec _ (CharConstant c) = dquotes (pretty c)
            prettyPrec _ (CharCode c) = "0" <> pretty (showHex c "") <> "X"
            prettyPrec _ (String s) = dquotes (pretty s)
            prettyPrec _ Nil = "NIL"
            prettyPrec _ (Set elements) = braces (hsep $ punctuate comma $ pretty <$> elements)
            prettyPrec _ (Read (Identity var)) = pretty var
            prettyPrec _ (FunctionCall (Identity fun) parameters) =
               pretty fun <> parens (hsep $ punctuate comma $ pretty <$> parameters)
            prettyPrec p (Not e) | p < 5 = "~" <> prettyPrec 5 e
            prettyPrec p e = parens (prettyPrec 0 e)

instance Pretty RelOp where
   pretty Equal = "="

instance Pretty (Element Identity) where
   pretty (Element e) = pretty e
   pretty (Range from to) = pretty from <+> ".." <+> pretty to

instance Pretty (Designator Identity) where
   pretty (Variable q) = pretty q
   pretty (Field record name) = pretty record <> dot <> pretty name
   pretty (Index array index) = pretty array <> brackets (pretty index)
   pretty (TypeGuard scrutinee typeName) = pretty scrutinee <> parens (pretty typeName)
   pretty (Dereference pointer) = pretty pointer <> "^"

instance Pretty (Type Identity) where
   pretty (TypeReference q) = pretty q
   pretty (ArrayType dimensions itemType) =
      "ARRAY" <+> hsep (punctuate comma $ pretty <$> toList dimensions) <+> "OF" <+> pretty itemType
   pretty (RecordType baseType fields) = vsep ["RECORD" <+> maybe mempty (parens . pretty) baseType,
                                               indent 3 (vsep $ punctuate semi $ pretty <$> fields),
                                               "END"]
   pretty (PointerType pointed) = "POINTER" <+> "TO" <+> pretty pointed
   pretty (ProcedureType parameters) = "PROCEDURE" <+> pretty parameters

instance Pretty QualIdent where
   pretty (QualIdent moduleName memberName) = pretty moduleName <> "." <> pretty memberName
   pretty (NonQualIdent localName) = pretty localName

instance Pretty (FieldList Identity) where
   pretty (FieldList names t) = hsep (punctuate comma $ pretty <$> toList names) <+> ":" <+> pretty t

instance Pretty ProcedureHeading where
   pretty (ProcedureHeading indirect ident parameters) =
      "PROCEDURE" <> (if indirect then "*" else mempty) <+> pretty ident <> pretty parameters

instance Pretty FormalParameters where
   pretty (FormalParameters sections result) =
      prettyList sections <+> maybe mempty (colon <+>) (pretty <$> result)

instance Pretty FPSection where
   prettyList sections = lparen <> hsep (punctuate comma $ pretty <$> sections) <> rparen
   pretty (FPSection var names t) =
      (if var then ("VAR" <+>) else id) $ hsep (punctuate comma $ pretty <$> toList names) <+> colon <+> pretty t

instance Pretty FormalType where
   pretty (ArrayOf itemType) = "ARRAY" <+> "OF" <+> pretty itemType
   pretty (FormalTypeReference name) = pretty name
   pretty (FormalProcedureType parameters) = "PROCEDURE" <+> pretty parameters
   
instance Pretty (ProcedureBody Identity) where
   pretty (ProcedureBody declarations body) =
      vsep ((indent 3 . pretty <$> declarations)
            ++ [maybe mempty (\statements-> vsep ["BEGIN", prettyBlock statements]) body])

instance Pretty (Statement Identity) where
   prettyList = vsep . punctuate semi . (pretty <$>)
   pretty EmptyStatement = mempty
   pretty (Assignment (Identity destination) expression) = pretty destination <+> ":=" <+> pretty expression
   pretty (ProcedureCall (Identity procedure) parameters) =
      pretty procedure <> maybe mempty (parens . hsep . punctuate comma . (pretty <$>)) parameters
   pretty (If (ifThen :| elsifs) fallback) = vsep [branch "IF" ifThen,
                                                   vsep (branch "ELSIF" <$> elsifs),
                                                   maybe mempty ("ELSE" <#>) (prettyBlock <$> fallback)]
      where branch kwd (condition, body) = vsep [kwd <+> pretty condition <+> "THEN",
                                                 prettyBlock body]
   pretty (CaseStatement scrutinee cases fallback) = vsep ["CASE" <+> pretty scrutinee <+> "OF",
                                                           pretty cases,
                                                           maybe mempty ("ELSE" <#>) (prettyBlock <$> fallback)]
                                                           
   pretty (While condition body) = vsep ["WHILE" <+> pretty condition,
                                         prettyBlock body,
                                         "END"]
   pretty (Repeat body condition) = vsep ["REPEAT",
                                          prettyBlock body,
                                          "UNTIL" <+> pretty condition]
   pretty (For index from to by body) = vsep ["FOR" <+> pretty index <+> ":=" <+> pretty from <+> "TO" <+> pretty to
                                              <+> maybe mempty ("BY" <+>) (pretty <$> by),
                                              prettyBlock body,
                                              "END"]
   pretty (Loop body) = vsep ["LOOP",
                              prettyBlock body,
                              "END"]
   pretty (With inner outer body) = vsep ["WITH" <+> pretty inner <+> colon <+> pretty outer <+> "DO",
                                          prettyBlock body,
                                          "END"]
   pretty Exit = "EXIT"
   pretty (Return result) = "RETURN" <+> maybe mempty pretty result
   
instance Pretty (Case Identity) where
   pretty (Case labels body) = vsep ["|" <+> pretty labels <+> colon,
                                     prettyBlock body]

instance Pretty (CaseLabels Identity) where
   pretty (SingleLabel expression) = pretty expression
   pretty (LabelRange from to) = pretty from <+> ".." <+> pretty to

prettyBlock statements = indent 3 (pretty $ runIdentity <$> statements)
a <#> b = vsep [a, b]
