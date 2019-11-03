{-# LANGUAGE FlexibleContexts, FlexibleInstances, OverloadedStrings, UndecidableInstances #-}

-- | This module exports the instances of the 'Pretty' type class necessary for printing of an Oberon abstract syntax
-- tree. Note that the AST cannot be ambiguous to be pretty-printed, so it must be resolved after parsing.

module Language.Oberon.Pretty (Precedence(Precedence)) where

import Data.Char (toUpper)
import Data.Functor.Identity (Identity(..))
import Data.List (intersperse)
import Data.List.NonEmpty (NonEmpty((:|)), toList)
import qualified Data.Text as Text
import Data.Text.Prettyprint.Doc
import Numeric (showHex)

import qualified Language.Oberon.Abstract as Abstract
import Language.Oberon.AST

data Precedence e = Precedence Int e

instance (Pretty (Abstract.Import l), Pretty (Abstract.Declaration l l Identity Identity),
          Pretty (Abstract.StatementSequence l l Identity Identity)) =>
         Pretty (Module λ l Identity Identity) where
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

instance (Abstract.Nameable l, Pretty (Abstract.IdentDef l), Pretty (Abstract.Type l l Identity Identity),
          Pretty (Abstract.Declaration l l Identity Identity),
          Pretty (Abstract.Expression l l Identity Identity), Pretty (Abstract.FormalParameters l l Identity Identity),
          Pretty (Abstract.ProcedureHeading l l Identity Identity),
          Pretty (Abstract.Block l l Identity Identity)) =>
         Pretty (Declaration λ l Identity Identity) where
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

instance  (Pretty (Precedence (Abstract.Expression l l Identity Identity)),
           Pretty (Abstract.Expression l l Identity Identity),
           Pretty (Abstract.Element l l Identity Identity),
           Pretty (Abstract.Designator l l Identity Identity),
           Pretty (Abstract.Value l l Identity Identity),
           Pretty (Abstract.QualIdent l)) => Pretty (Expression λ l Identity Identity) where
   pretty e = pretty (Precedence 0 e)
   
instance  (Pretty (Precedence (Abstract.Expression l l Identity Identity)),
           Pretty (Abstract.Expression l l Identity Identity),
           Pretty (Abstract.Element l l Identity Identity),
           Pretty (Abstract.Designator l l Identity Identity),
           Pretty (Abstract.QualIdent l),
           Pretty (Abstract.Value l l Identity Identity)) =>
          Pretty (Precedence (Expression λ l Identity Identity)) where
   pretty (Precedence 0 (Relation op left right)) = prettyPrec' 1 left <+> pretty op <+> prettyPrec' 1 right
   pretty (Precedence 0 (IsA left right)) = prettyPrec' 1 left <+> "IS" <+> pretty right
   pretty (Precedence p (Add left right)) | p < 2 = prettyPrec' 2 left <> "+" <> prettyPrec' 2 right
   pretty (Precedence p (Subtract left right)) | p < 2 = prettyPrec' 2 left <> "-" <> prettyPrec' 2 right
   pretty (Precedence p (Or left right)) | p < 2 = prettyPrec' 2 left <+> "OR" <+> prettyPrec' 2 right
   pretty (Precedence p (Positive e)) | p < 3 = "+" <> prettyPrec' 3 e
   pretty (Precedence p (Negative e)) | p < 3 = "-" <> prettyPrec' 3 e
   pretty (Precedence p (Multiply left right)) | p < 4 = prettyPrec' 4 left <> "*" <> prettyPrec' 4 right
   pretty (Precedence p (Divide left right)) | p < 4 = prettyPrec' 4 left <> "/" <> prettyPrec' 4 right
   pretty (Precedence p (IntegerDivide left right)) | p < 4 = prettyPrec' 4 left <+> "DIV" <+> prettyPrec' 4 right
   pretty (Precedence p (Modulo left right)) | p < 4 = prettyPrec' 4 left <+> "MOD" <+> prettyPrec' 4 right
   pretty (Precedence p (And left right)) | p < 4 = prettyPrec' 4 left <+> "&" <+> prettyPrec' 4 right
   pretty (Precedence _ (Set elements)) = braces (hsep $ punctuate comma $ pretty . runIdentity <$> elements)
   pretty (Precedence _ (Read (Identity var))) = pretty var
   pretty (Precedence _ (FunctionCall (Identity fun) parameters)) =
      pretty fun <> parens (hsep $ punctuate comma $ pretty . runIdentity <$> parameters)
   pretty (Precedence _ (Literal (Identity val))) = pretty val
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

instance Pretty (Abstract.Expression l l Identity Identity) => Pretty (Element λ l Identity Identity) where
   pretty (Element e) = pretty e
   pretty (Range from to) = pretty from <+> ".." <+> pretty to

instance Pretty (Value λ l Identity Identity) where
   pretty (Boolean False) = "FALSE"
   pretty (Boolean True) = "TRUE"
   pretty (Integer n) = pretty n
   pretty (Real r) = pretty (map toUpper $ show r)
   pretty (CharCode c) = "0" <> pretty (showHex c "") <> "X"
   pretty (String s)
      | Text.any (== '"') s = squotes (pretty s)
      | otherwise = dquotes (pretty s)
   pretty Nil = "NIL"
   pretty (Builtin name) = pretty name


instance (Pretty (Abstract.QualIdent l), Pretty (Abstract.Designator l l Identity Identity),
          Pretty (Abstract.Expression l l Identity Identity)) => Pretty (Designator λ l Identity Identity) where
   pretty (Variable q) = pretty q
   pretty (Field record name) = pretty record <> dot <> pretty name
   pretty (Index array indexes) = pretty array <> brackets (hsep $ punctuate comma $ pretty <$> toList indexes)
   pretty (TypeGuard scrutinee typeName) = pretty scrutinee <> parens (pretty typeName)
   pretty (Dereference pointer) = pretty pointer <> "^"

instance (Pretty (Abstract.FormalParameters l l Identity Identity), Pretty (Abstract.FieldList l l Identity Identity),
          Pretty (Abstract.ConstExpression l l Identity Identity), Pretty (Abstract.Type l l Identity Identity),
          Pretty (Abstract.BaseType l)) => Pretty (Type λ l Identity Identity) where
   pretty (TypeReference q) = pretty q
   pretty (ArrayType dimensions itemType) =
      "ARRAY" <+> hsep (punctuate comma $ pretty . runIdentity <$> dimensions) <+> "OF" <+> pretty itemType
   pretty (RecordType baseType fields) = vsep ["RECORD" <+> foldMap (parens . pretty) baseType,
                                               indent 3 (vsep $ punctuate semi $ pretty <$> fields),
                                               "END"]
   pretty (PointerType pointed) = "POINTER" <+> "TO" <+> pretty pointed
   pretty (ProcedureType parameters) = "PROCEDURE" <+> pretty parameters

instance Pretty (QualIdent l) where
   pretty (QualIdent moduleName memberName) = pretty moduleName <> "." <> pretty memberName
   pretty (NonQualIdent localName) = pretty localName

instance (Pretty (Abstract.IdentDef l), Pretty (Abstract.Type l l Identity Identity)) =>
         Pretty (FieldList λ l Identity Identity) where
   pretty (FieldList names t) = hsep (punctuate comma $ pretty <$> toList names) <+> ":" <+> pretty t

instance (Pretty (Abstract.IdentDef l), Pretty (Abstract.FormalParameters l l Identity Identity),
          Pretty (Abstract.Type l l Identity Identity)) =>
         Pretty (ProcedureHeading λ l Identity Identity) where
   pretty (ProcedureHeading indirect ident parameters) =
      "PROCEDURE" <> (if indirect then "* " else space) <> pretty ident <> pretty parameters
   pretty (TypeBoundHeading var receiverName receiverType indirect ident parameters) =
      "PROCEDURE" <> space 
      <> parens ((if var then "VAR " else mempty) <> pretty receiverName <> colon <+> pretty receiverType)
      <> space <> (if indirect then "* " else space) <> pretty ident <> pretty parameters

instance (Pretty (Abstract.FPSection l l Identity Identity),
          Pretty (Abstract.ReturnType l)) => Pretty (FormalParameters λ l Identity Identity) where
   pretty (FormalParameters sections result) =
      lparen <> hsep (punctuate semi $ pretty <$> sections) <> rparen <> foldMap (colon <+>) (pretty <$> result)

instance Pretty (Abstract.Type l l Identity Identity) => Pretty (FPSection λ l Identity Identity) where
   pretty (FPSection var names t) =
      (if var then ("VAR" <+>) else id) $ hsep (punctuate comma $ pretty <$> names) <+> colon <+> pretty t
   
instance (Pretty (Abstract.Declaration l l Identity Identity), Pretty (Abstract.StatementSequence l l Identity Identity)) =>
         Pretty (Block λ l Identity Identity) where
   pretty (Block declarations body) =
      vsep ((indent 3 . pretty <$> declarations)
            ++ foldMap (\statements-> ["BEGIN", prettyBlock statements]) body)

instance Pretty (Abstract.Statement l l Identity Identity) => Pretty (StatementSequence λ l Identity Identity) where
   pretty (StatementSequence statements) = pretty (runIdentity <$> statements)

instance (Pretty (Abstract.ConstExpression l l Identity Identity),
          Pretty (Abstract.Designator l l Identity Identity),
          Pretty (Abstract.Case l l Identity Identity),
          Pretty (Abstract.ConditionalBranch l l Identity Identity),
          Pretty (Abstract.WithAlternative l l Identity Identity),
          Pretty (Abstract.StatementSequence l l Identity Identity)) => Pretty (Statement λ l Identity Identity) where
   prettyList l = vsep (dropEmptyTail $ punctuate semi $ pretty <$> l)
      where dropEmptyTail
               | not (null l), EmptyStatement <- last l = init
               | otherwise = id
   pretty EmptyStatement = mempty
   pretty (Assignment (Identity destination) expression) = pretty destination <+> ":=" <+> pretty expression
   pretty (ProcedureCall (Identity procedure) parameters) =
      pretty procedure <> foldMap (parens . hsep . punctuate comma . (pretty <$>)) parameters
   pretty (If (ifThen :| elsifs) fallback) = vsep ("IF" <+> pretty ifThen
                                                   : ((("ELSIF" <+>) . pretty) <$> elsifs)
                                                    ++ foldMap (\x-> ["ELSE", prettyBlock x]) fallback
                                                    ++ ["END"])
   pretty (CaseStatement scrutinee cases fallback) = vsep ["CASE" <+> pretty scrutinee <+> "OF",
                                                           align (encloseSep mempty mempty "| " $ pretty <$> cases),
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

instance (Pretty (Abstract.Expression l l Identity Identity),
          Pretty (Abstract.StatementSequence l l Identity Identity)) =>
         Pretty (ConditionalBranch λ l Identity Identity) where
   pretty (ConditionalBranch condition body) = vsep [pretty condition <+> "THEN",
                                                     prettyBlock body]
   
instance (Pretty (Abstract.CaseLabels l l Identity Identity),
          Pretty (Abstract.ConstExpression l l Identity Identity),
          Pretty (Abstract.StatementSequence l l Identity Identity)) => Pretty (Case λ l Identity Identity) where
   pretty (Case labels body) = vsep [hsep (punctuate comma (pretty <$> toList labels)) <+> colon,
                                     prettyBlock body]
   
instance (Pretty (Abstract.QualIdent l), Pretty (Abstract.StatementSequence l l Identity Identity)) =>
         Pretty (WithAlternative λ l Identity Identity) where
   pretty (WithAlternative name t body) = vsep [pretty name <+> colon <+> pretty t <+> "DO",
                                                prettyBlock body]

instance Pretty (Abstract.ConstExpression l l Identity Identity) => Pretty (CaseLabels λ l Identity Identity) where
   pretty (SingleLabel expression) = pretty expression
   pretty (LabelRange from to) = pretty from <+> ".." <+> pretty to

prettyBlock :: Pretty (Abstract.StatementSequence l l Identity Identity) =>
               Identity (Abstract.StatementSequence l l Identity Identity) -> Doc ann
prettyBlock (Identity statements) = indent 3 (pretty statements)

a <#> b = vsep [a, b]
