{-# LANGUAGE FlexibleContexts, FlexibleInstances, OverloadedStrings, UndecidableInstances #-}

-- | This module exports the instances of the 'Pretty' type class necessary for printing of an Oberon abstract syntax
-- tree. Note that the AST cannot be ambiguous to be pretty-printed, so it must be resolved after parsing.

module Language.Oberon.Pretty () where

import Data.Functor.Identity (Identity(..))
import Data.List (intersperse)
import Data.List.NonEmpty (NonEmpty((:|)), fromList, toList)
import qualified Data.Text as Text
import Data.Text.Prettyprint.Doc
import Numeric (showHex)
import Transformation.Deep as Deep (Product(Pair))

import qualified Language.Oberon.Abstract as Abstract
import Language.Oberon.AST

data Precedence e = Precedence Int e

instance (Pretty (Abstract.Declaration l Identity Identity), Pretty (Abstract.StatementSequence l Identity Identity)) =>
         Pretty (Module l Identity Identity) where
   pretty (Module name imports declarations body) =
      vsep $ intersperse mempty $
      ["MODULE" <+> pretty name <> semi,
       if null imports then mempty
       else "IMPORT" <+> align (fillSep (punctuate comma $ prettyImport <$> imports)) <> semi]
      <> (pretty <$> declarations)
      <> [vsep (foldMap (\statements-> ["BEGIN" <#> indent 3 (pretty statements)]) body
                <> ["END" <+> pretty name <> "." <> line])]
      where prettyImport (Nothing, mod) = pretty mod
            prettyImport (Just inner, mod) = pretty inner <> ":=" <+> pretty mod

instance (Abstract.Nameable l, Pretty (Abstract.IdentDef l), Pretty (Abstract.Type l Identity Identity),
          Pretty (Abstract.Declaration l Identity Identity),
          Pretty (Abstract.Expression l Identity Identity), Pretty (Abstract.FormalParameters l Identity Identity),
          Pretty (Abstract.ProcedureHeading l Identity Identity),
          Pretty (Abstract.ProcedureBody l Identity Identity)) =>
         Pretty (Declaration l Identity Identity) where
   pretty (ConstantDeclaration ident (Identity expr)) = "CONST" <+> pretty ident <+> "=" <+> pretty expr <> semi
   pretty (TypeDeclaration ident typeDef) = "TYPE" <+> pretty ident <+> "=" <+> pretty typeDef <> semi
   pretty (VariableDeclaration idents varType) =
      "VAR" <+> hsep (punctuate comma $ pretty <$> toList idents) <+> colon <+> pretty varType <> semi
   pretty (ProcedureDeclaration heading body) = vsep [pretty heading <> semi,
                                                      pretty body,
                                                      "END" <+> pretty (Abstract.getProcedureName $ runIdentity heading)
                                                      <> semi]
   pretty (ForwardDeclaration ident parameters) = "PROCEDURE" <+> "^" <+> pretty ident <+> pretty parameters <> semi

instance Pretty (IdentDef l) where
   pretty (IdentDef name Exported) = pretty name <> "*"
   pretty (IdentDef name ReadOnly) = pretty name <> "-"
   pretty (IdentDef name PrivateOnly) = pretty name

instance  (Pretty (Precedence (Abstract.Expression l Identity Identity)),
           Pretty (Abstract.Expression l Identity Identity),
           Pretty (Abstract.Element l Identity Identity),
           Pretty (Abstract.Designator l Identity Identity)) => Pretty (Expression l Identity Identity) where
   pretty e = pretty (Precedence 0 e)
   
instance  (Pretty (Precedence (Abstract.Expression l Identity Identity)),
           Pretty (Abstract.Expression l Identity Identity),
           Pretty (Abstract.Element l Identity Identity),
           Pretty (Abstract.Designator l Identity Identity)) =>
          Pretty (Precedence (Expression l Identity Identity)) where
   pretty (Precedence 0 (Relation op left right)) = prettyPrec' 1 left <+> pretty op <+> prettyPrec' 1 right
   pretty (Precedence 0 (IsA left right)) = prettyPrec' 1 left <+> "IS" <+> pretty right
   pretty (Precedence p (Positive e)) | p < 2 = "+" <> prettyPrec' 2 e
   pretty (Precedence p (Negative e)) | p < 2 = "-" <> prettyPrec' 2 e
   pretty (Precedence p (Add left right)) | p < 3 = prettyPrec' 3 left <> "+" <> prettyPrec' 3 right
   pretty (Precedence p (Subtract left right)) | p < 3 = prettyPrec' 3 left <> "-" <> prettyPrec' 3 right
   pretty (Precedence p (Or left right)) | p < 3 = prettyPrec' 3 left <+> "OR" <+> prettyPrec' 3 right
   pretty (Precedence p (Multiply left right)) | p < 4 = prettyPrec' 4 left <> "*" <> prettyPrec' 4 right
   pretty (Precedence p (Divide left right)) | p < 4 = prettyPrec' 4 left <> "/" <> prettyPrec' 4 right
   pretty (Precedence p (IntegerDivide left right)) | p < 4 = prettyPrec' 4 left <+> "DIV" <+> prettyPrec' 4 right
   pretty (Precedence p (Modulo left right)) | p < 4 = prettyPrec' 4 left <+> "MOD" <+> prettyPrec' 4 right
   pretty (Precedence p (And left right)) | p < 4 = prettyPrec' 4 left <+> "&" <+> prettyPrec' 4 right
   pretty (Precedence _ (Integer n)) = pretty n
   pretty (Precedence _ (Real r)) = pretty r
   pretty (Precedence _ (CharConstant c@'"')) = squotes (pretty c)
   pretty (Precedence _ (CharConstant c)) = dquotes (pretty c)
   pretty (Precedence _ (CharCode c)) = "0" <> pretty (showHex c "") <> "X"
   pretty (Precedence _ (String s))
      | Text.any (== '"') s = squotes (pretty s)
      | otherwise = dquotes (pretty s)
   pretty (Precedence _ Nil) = "NIL"
   pretty (Precedence _ (Set elements)) = braces (hsep $ punctuate comma $ pretty . runIdentity <$> elements)
   pretty (Precedence _ (Read (Identity var))) = pretty var
   pretty (Precedence _ (FunctionCall (Identity fun) parameters)) =
      pretty fun <> parens (hsep $ punctuate comma $ pretty . runIdentity <$> parameters)
   pretty (Precedence p (Not e)) | p < 5 = "~" <> prettyPrec' 5 e
   pretty (Precedence _ e) = parens (pretty e)

prettyPrec' p (Identity e) = pretty (Precedence p e)

instance Pretty RelOp where
   pretty Equal = "="
   pretty Unequal = "#"
   pretty Less = "<"
   pretty LessOrEqual =  "<="
   pretty Greater = ">"
   pretty GreaterOrEqual = ">="
   pretty In = "IN"

instance Pretty (Abstract.Expression l Identity Identity) => Pretty (Element l Identity Identity) where
   pretty (Element e) = pretty e
   pretty (Range from to) = pretty from <+> ".." <+> pretty to

instance (Pretty (Abstract.Designator l Identity Identity),
          Pretty (Abstract.Expression l Identity Identity)) => Pretty (Designator l Identity Identity) where
   pretty (Variable q) = pretty q
   pretty (Field record name) = pretty record <> dot <> pretty name
   pretty (Index array indexes) = pretty array <> brackets (hsep $ punctuate comma $ pretty <$> toList indexes)
   pretty (TypeGuard scrutinee typeName) = pretty scrutinee <> parens (pretty typeName)
   pretty (Dereference pointer) = pretty pointer <> "^"

instance (Pretty (Abstract.FormalParameters l Identity Identity), Pretty (Abstract.FieldList l Identity Identity),
          Pretty (Abstract.ConstExpression l Identity Identity), Pretty (Abstract.Type l Identity Identity)) =>
         Pretty (Type l Identity Identity) where
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

instance (Pretty (Abstract.IdentDef l), Pretty (Abstract.Type l Identity Identity)) =>
         Pretty (FieldList l Identity Identity) where
   pretty (FieldList names t) = hsep (punctuate comma $ pretty <$> toList names) <+> ":" <+> pretty t
   pretty EmptyFieldList = mempty

instance (Pretty (Abstract.IdentDef l), Pretty (Abstract.FormalParameters l Identity Identity),
          Pretty (Abstract.Type l Identity Identity)) =>
         Pretty (ProcedureHeading l Identity Identity) where
   pretty (ProcedureHeading indirect ident parameters) =
      "PROCEDURE" <> (if indirect then "* " else space) <> pretty ident <> pretty parameters
   pretty (TypeBoundHeading var receiverName receiverType indirect ident parameters) =
      "PROCEDURE" <> space 
      <> parens ((if var then "VAR " else mempty) <> pretty receiverName <> colon <+> pretty receiverType)
      <> space <> (if indirect then "* " else space) <> pretty ident <> pretty parameters

instance (Pretty (Abstract.FPSection l Identity Identity),
          Pretty (Abstract.Type l Identity Identity)) => Pretty (FormalParameters l Identity Identity) where
   pretty (FormalParameters sections result) =
      lparen <> hsep (punctuate semi $ pretty <$> sections) <> rparen <> foldMap (colon <+>) (pretty <$> result)

instance Pretty (Abstract.Type l Identity Identity) => Pretty (FPSection l Identity Identity) where
   pretty (FPSection var names t) =
      (if var then ("VAR" <+>) else id) $ hsep (punctuate comma $ pretty <$> toList names) <+> colon <+> pretty t
   
instance (Pretty (Abstract.Declaration l Identity Identity), Pretty (Abstract.StatementSequence l Identity Identity)) =>
         Pretty (ProcedureBody l Identity Identity) where
   pretty (ProcedureBody declarations body) =
      vsep ((indent 3 . pretty <$> declarations)
            ++ foldMap (\statements-> ["BEGIN", prettyBlock statements]) body)

instance Pretty (Abstract.Statement l Identity Identity) => Pretty (StatementSequence l Identity Identity) where
   pretty (StatementSequence statements) = pretty (runIdentity <$> statements)

instance (Pretty (Abstract.ConstExpression l Identity Identity),
          Pretty (Abstract.Designator l Identity Identity),
          Pretty (Abstract.Case l Identity Identity),
          Pretty (Abstract.WithAlternative l Identity Identity),
          Pretty (Abstract.StatementSequence l Identity Identity)) => Pretty (Statement l Identity Identity) where
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
      where branch kwd (Identity (Deep.Pair (Identity condition) (Identity body))) =
               vsep [kwd <+> pretty condition <+> "THEN",
                     prettyBlock (Identity body)]
   pretty (CaseStatement scrutinee cases fallback) = vsep ["CASE" <+> pretty scrutinee <+> "OF",
                                                           align (encloseSep mempty mempty "| "
                                                                  $ pretty <$> toList cases),
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
   
instance (Pretty (Abstract.CaseLabels l Identity Identity),
          Pretty (Abstract.ConstExpression l Identity Identity),
          Pretty (Abstract.StatementSequence l Identity Identity)) => Pretty (Case l Identity Identity) where
   pretty (Case labels body) = vsep [hsep (punctuate comma (pretty <$> toList labels)) <+> colon,
                                     prettyBlock body]
   pretty EmptyCase = mempty
   
instance Pretty (Abstract.StatementSequence l Identity Identity) => Pretty (WithAlternative l Identity Identity) where
   pretty (WithAlternative name t body) = vsep [pretty name <+> colon <+> pretty t <+> "DO",
                                                prettyBlock body]

instance Pretty (Abstract.ConstExpression l Identity Identity) => Pretty (CaseLabels l Identity Identity) where
   pretty (SingleLabel expression) = pretty expression
   pretty (LabelRange from to) = pretty from <+> ".." <+> pretty to

prettyBlock :: Pretty (Abstract.StatementSequence l Identity Identity) =>
               Identity (Abstract.StatementSequence l Identity Identity) -> Doc ann
prettyBlock (Identity statements) = indent 3 (pretty statements)

a <#> b = vsep [a, b]
