{-# LANGUAGE FlexibleInstances, OverloadedStrings #-}

module Language.Oberon.Pretty where

import Data.Functor.Identity (Identity(..))
import Data.List (intersperse)
import Data.List.NonEmpty (NonEmpty((:|)), fromList, toList)
import Data.Text.Prettyprint.Doc
import Numeric (showHex)

import Language.Oberon.AST

instance Pretty (Module Identity) where
   pretty (Module name imports declarations body name') =
      vsep $ intersperse mempty $
      ["MODULE" <+> pretty name <> semi,
       if null imports then mempty
       else "IMPORT" <+> align (fillSep (punctuate comma $ prettyImport <$> imports)) <> semi]
      <> (pretty <$> declarations)
      <> [vsep (foldMap (\statements-> ["BEGIN" <#> prettyBlock statements]) body
                <> ["END" <+> pretty name' <> "." <> line])]
      where prettyImport (Nothing, mod) = pretty mod
            prettyImport (Just inner, mod) = pretty inner <> ":=" <+> pretty mod

instance Pretty (Declaration Identity) where
   pretty (ConstantDeclaration ident (Identity expr)) = "CONST" <+> pretty ident <+> "=" <+> pretty expr <> semi
   pretty (TypeDeclaration ident typeDef) = "TYPE" <+> pretty ident <+> "=" <+> pretty typeDef <> semi
   pretty (VariableDeclaration idents varType) =
      "VAR" <+> hsep (punctuate comma $ pretty <$> toList idents) <+> colon <+> pretty varType <> semi
   pretty (ProcedureDeclaration heading body name) = vsep [pretty heading <> semi,
                                                           pretty body,
                                                           "END" <+> pretty name <> semi]
   pretty (ForwardDeclaration ident parameters) = "PROCEDURE" <+> "^" <+> pretty ident <+> pretty parameters <> semi

instance Pretty IdentDef where
   pretty (IdentDef name Exported) = pretty name <> "*"
   pretty (IdentDef name ReadOnly) = pretty name <> "-"
   pretty (IdentDef name PrivateOnly) = pretty name

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
   pretty Unequal = "#"
   pretty Less = "<"
   pretty LessOrEqual =  "<="
   pretty Greater = ">"
   pretty GreaterOrEqual = ">="
   pretty In = "IN"
   pretty Is = "IS"

instance Pretty (Element Identity) where
   pretty (Element e) = pretty e
   pretty (Range from to) = pretty from <+> ".." <+> pretty to

instance Pretty (Designator Identity) where
   pretty (Variable q) = pretty q
   pretty (Field record name) = pretty record <> dot <> pretty name
   pretty (Index array indexes) = pretty array <> brackets (hsep $ punctuate comma $ pretty <$> toList indexes)
   pretty (TypeGuard scrutinee typeName) = pretty scrutinee <> parens (pretty typeName)
   pretty (Dereference pointer) = pretty pointer <> "^"

instance Pretty (Type Identity) where
   pretty (TypeReference q) = pretty q
   pretty (ArrayType dimensions itemType) =
      "ARRAY" <+> hsep (punctuate comma $ pretty . runIdentity <$> dimensions) <+> "OF" <+> pretty itemType
   pretty (RecordType baseType fields) = vsep ["RECORD" <+> foldMap (parens . pretty) baseType,
                                               indent 3 (vsep $ punctuate semi $ pretty <$> toList fields),
                                               "END"]
   pretty (PointerType pointed) = "POINTER" <+> "TO" <+> pretty pointed
   pretty (ProcedureType parameters) = "PROCEDURE" <+> pretty parameters

instance Pretty QualIdent where
   pretty (QualIdent moduleName memberName) = pretty moduleName <> "." <> pretty memberName
   pretty (NonQualIdent localName) = pretty localName

instance Pretty (FieldList Identity) where
   pretty (FieldList names t) = hsep (punctuate comma $ pretty <$> toList names) <+> ":" <+> pretty t
   pretty EmptyFieldList = mempty

instance Pretty (ProcedureHeading Identity) where
   pretty (ProcedureHeading receiver indirect ident parameters) =
      "PROCEDURE" <> (if indirect then "* " else space) <> foldMap prettyReceiver receiver
      <> pretty ident <> pretty parameters
      where prettyReceiver (var, name, t) = parens ((if var then "VAR " else mempty)
                                                        <> pretty name <> colon <+> pretty t)
                                            <> space

instance Pretty (FormalParameters Identity) where
   pretty (FormalParameters sections result) =
      prettyList sections <> foldMap (colon <+>) (pretty <$> result)

instance Pretty (FPSection Identity) where
   prettyList sections = lparen <> hsep (punctuate semi $ pretty <$> sections) <> rparen
   pretty (FPSection var names t) =
      (if var then ("VAR" <+>) else id) $ hsep (punctuate comma $ pretty <$> toList names) <+> colon <+> pretty t
   
instance Pretty (ProcedureBody Identity) where
   pretty (ProcedureBody declarations body) =
      vsep ((indent 3 . pretty <$> declarations)
            ++ foldMap (\statements-> ["BEGIN", prettyBlock statements]) body)

instance Pretty (Statement Identity) where
   prettyList l = vsep (dropEmptyTail $ punctuate semi $ pretty <$> l)
      where dropEmptyTail
               | not (null l), EmptyStatement <- last l = init
               | otherwise = id
   pretty EmptyStatement = mempty
   pretty (Assignment (Identity destination) expression) = pretty destination <+> ":=" <+> pretty expression
   pretty (ProcedureCall (Identity procedure) parameters) =
      pretty procedure <> foldMap (parens . hsep . punctuate comma . (pretty <$>)) parameters
   pretty (If (ifThen :| elsifs) fallback) = vsep (branch "IF" ifThen
                                                   : (branch "ELSIF" <$> elsifs)
                                                    ++ foldMap (\x-> ["ELSE", prettyBlock x]) fallback
                                                    ++ ["END"])
      where branch kwd (condition, body) = vsep [kwd <+> pretty condition <+> "THEN",
                                                 prettyBlock body]
   pretty (CaseStatement scrutinee cases fallback) = vsep ["CASE" <+> pretty scrutinee <+> "OF",
                                                           pretty cases,
                                                           foldMap ("ELSE" <#>) (prettyBlock <$> fallback),
                                                           "END"]
                                                           
   pretty (While condition body) = vsep ["WHILE" <+> pretty condition <+> "DO",
                                         prettyBlock body,
                                         "END"]
   pretty (Repeat body condition) = vsep ["REPEAT",
                                          prettyBlock body,
                                          "UNTIL" <+> pretty condition]
   pretty (For index from to by body) = vsep ["FOR" <+> pretty index <+> ":=" <+> pretty from <+> "TO" <+> pretty to
                                              <+> foldMap ("BY" <+>) (pretty <$> by) <+> "DO",
                                              prettyBlock body,
                                              "END"]
   pretty (Loop body) = vsep ["LOOP",
                              prettyBlock body,
                              "END"]
   pretty (With alternatives fallback) =
      "WITH" <+>
      vsep (punctuate pipe (pretty <$> toList alternatives) ++ 
            foldMap (\x-> ["ELSE", prettyBlock x]) fallback ++
            ["END"])
   pretty Exit = "EXIT"
   pretty (Return result) = "RETURN" <+> foldMap pretty result
   
instance Pretty (Case Identity) where
   pretty (Case labels body) = vsep ["|" <+> pretty labels <+> colon,
                                     prettyBlock body]
   pretty EmptyCase = mempty
   
instance Pretty (WithAlternative Identity) where
   pretty (WithAlternative name t body) = vsep [pretty name <+> colon <+> pretty t <+> "DO",
                                                prettyBlock body]

instance Pretty (CaseLabels Identity) where
   pretty (SingleLabel expression) = pretty expression
   pretty (LabelRange from to) = pretty from <+> ".." <+> pretty to

prettyBlock statements = indent 3 (pretty $ runIdentity <$> statements)
a <#> b = vsep [a, b]
