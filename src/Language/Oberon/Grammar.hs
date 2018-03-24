{-# Language OverloadedStrings, Rank2Types, RecordWildCards, TypeFamilies, TemplateHaskell #-}

-- * From http://www.ethoberon.ethz.ch/EBNF.html
--   Extracted from the book Programmieren in Oberon - Das neue Pascal by N. Wirth and M. Reiser and translated by J. Templ.

module Language.Oberon.Grammar where

import Control.Applicative
import Control.Monad (guard)
import Data.Char
import Data.List.NonEmpty (NonEmpty((:|)), fromList, toList)
import Data.Monoid ((<>), Endo(Endo, appEndo))
import Numeric (readHex)
import Data.Text (Text, unpack)
import Text.Grampa
import Text.Grampa.ContextFree.LeftRecursive (Parser)
import Text.Parser.Combinators (sepBy, sepBy1, sepByNonEmpty)

import qualified Rank2
import qualified Rank2.TH

import Language.Oberon.AST

import Prelude hiding (length, takeWhile)

data OberonGrammar f p = OberonGrammar {
   module_prod :: p (Module f),
   ident :: p Ident,
   letter :: p Text,
   digit :: p Text,
   importList :: p [Import],
   import_prod :: p Import,
   declarationSequence :: p [Declaration f],
   constantDeclaration :: p (Declaration f),
   identdef :: p IdentDef,
   constExpression :: p (Expression f),
   expression :: p (Expression f),
   simpleExpression :: p (Expression f),
   term :: p (Expression f),
   factor :: p (Expression f),
   number :: p (Expression f),
   integer :: p (Expression f),
   hexDigit :: p Text,
   real :: p (Expression f),
   scaleFactor :: p Text,
   charConstant :: p (Expression f),
   string_prod :: p Text,
   set :: p (Expression f),
   element :: p (Element f),
   designator :: p (Designator f),
   expList :: p (NonEmpty (Expression f)),
   actualParameters :: p [(Expression f)],
   mulOperator :: p (BinOp f),
   addOperator :: p (BinOp f),
   relation :: p RelOp,
   typeDeclaration :: p (Declaration f),
   type_prod :: p (Type f),
   qualident :: p QualIdent,
   arrayType :: p (Type f),
   length :: p (Expression f),
   recordType :: p (Type f),
   baseType :: p QualIdent,
   fieldListSequence :: p (FieldListSequence f),
   fieldList :: p (FieldList f),
   identList :: p IdentList,
   pointerType :: p (Type f),
   procedureType :: p (Type f),
   variableDeclaration :: p (Declaration f),
   procedureDeclaration :: p (Declaration f),
   procedureHeading :: p ProcedureHeading,
   formalParameters :: p FormalParameters,
   fPSection :: p FPSection,
   formalType :: p FormalType,
   procedureBody :: p (ProcedureBody f),
   forwardDeclaration :: p (Declaration f),
   statementSequence :: p [Ambiguous (Statement f)],
   statement :: p (Statement f),
   assignment :: p (Statement f),
   procedureCall :: p (Statement f),
   ifStatement :: p (Statement f),
   caseStatement :: p (Statement f),
   case_prod :: p (Case f),
   caseLabelList :: p (NonEmpty (CaseLabels f)),
   caseLabels :: p (CaseLabels f),
   whileStatement :: p (Statement f),
   repeatStatement :: p (Statement f),
   forStatement :: p (Statement f),
   loopStatement :: p (Statement f),
   withStatement :: p (Statement f)}

newtype BinOp f = BinOp {applyBinOp :: (Expression f -> Expression f -> Expression f)}

instance Show (BinOp f) where
   show = const "BinOp{}"

$(Rank2.TH.deriveAll ''OberonGrammar)

instance Lexical (OberonGrammar f) where
   type LexicalConstraint p (OberonGrammar f) s = (s ~ Text, p ~ Parser)
   lexicalComment = string "(*"
                    *> skipMany (notFollowedBy (string "*)") *> anyToken *> takeCharsWhile (/= '*'))
                    <* string "*)"
   lexicalWhiteSpace = takeCharsWhile isSpace *> skipMany (lexicalComment *> takeCharsWhile isSpace)
   isIdentifierStartChar = isLetter
   isIdentifierFollowChar = isAlphaNum
   identifierToken word = lexicalToken (do w <- word
                                           guard (w `notElem` reservedWords)
                                           return w)

oberonGrammar, oberonDefinitionGrammar :: Grammar (OberonGrammar Ambiguous) Parser Text
oberonGrammar = fixGrammar grammar
oberonDefinitionGrammar = fixGrammar definitionGrammar

grammar, definitionGrammar :: GrammarBuilder (OberonGrammar Ambiguous) (OberonGrammar Ambiguous) Parser Text

definitionGrammar g@OberonGrammar{..} = (grammar g){
   module_prod = Module <$ (lexicalWhiteSpace *> keyword "DEFINITION") <*> ident <* delimiter ";"
                 <*> moptional importList <*> declarationSequence
                 <*> pure Nothing <* keyword "END" <*> ident <* delimiter ".",
   procedureDeclaration = ProcedureDeclaration <$> procedureHeading
                          <*> (pure $ ProcedureBody [] Nothing) <*> pure mempty,
   identdef = IdentDef <$> ident <*> pure True <* optional (delimiter "*")}
   
grammar OberonGrammar{..} = OberonGrammar{
   module_prod = Module <$ (lexicalWhiteSpace *> keyword "MODULE") <*> ident <* delimiter ";"
                 <*> moptional importList <*> declarationSequence
                 <*> optional (keyword "BEGIN" *> statementSequence) <* keyword "END" <*> ident <* delimiter ".",
   ident = identifier,
   letter = satisfyCharInput isLetter,
   digit = satisfyCharInput isDigit,
   importList = keyword "IMPORT" *> sepBy1 import_prod (delimiter ",") <* delimiter ";",
   import_prod = (,) <$> optional (ident <* delimiter ":=") <*> ident,
   declarationSequence = concatMany (keyword "CONST" *> many (constantDeclaration <* delimiter ";")
                                     <|> keyword "TYPE" *> many (typeDeclaration <* delimiter ";")
                                     <|> keyword "VAR" *> many (variableDeclaration <* delimiter ";"))
                         <> many (procedureDeclaration <* delimiter ";"
                                  <|> forwardDeclaration <* delimiter ";"),
   constantDeclaration = ConstantDeclaration <$> identdef <* delimiter "=" <*> constExpression,
   identdef = IdentDef <$> ident <*> (True <$ delimiter "*" <|> pure False),
   constExpression = expression,
   expression = simpleExpression <**> (pure id <|> (flip . Relation) <$> relation <*> simpleExpression),
   simpleExpression = (Positive <$ operator "+" <|> Negative <$ operator "-" <|> pure id)
                      <*> (term <**> (appEndo <$> concatMany (Endo <$> (flip . applyBinOp <$> addOperator <*> term)))),
   term = factor <**> (appEndo <$> concatMany (Endo <$> (flip . applyBinOp <$> mulOperator <*> factor))),
   factor  =  number
              <|> charConstant
              <|> String <$> string_prod
              <|> Nil <$ keyword "NIL"
              <|> set
              <|> Read <$> ambiguous designator
              <|> FunctionCall <$> ambiguous designator <*> actualParameters
              <|> delimiter "(" *> expression <* delimiter ")"
              <|> Not <$ operator "~" <*> factor,
   number  =  integer <|> real,
   integer = Integer <$> lexicalToken (digit <> (takeCharsWhile isDigit <|> takeCharsWhile isHexDigit <> string "H")),
   hexDigit = satisfyCharInput isHexDigit,
   real = Real <$> lexicalToken (digit <> takeCharsWhile isDigit <> string "."
                                 *> takeCharsWhile isDigit <> moptional scaleFactor),
   scaleFactor = (string "E" <|> string "D") <> moptional (string "+" <|> string "-") <> digit <> takeCharsWhile isDigit,
   charConstant = lexicalToken (CharConstant <$ char '"' <*> anyChar <* char '"'
                                <|> CharCode . fst . head . readHex . unpack
                                <$> (digit <> takeCharsWhile isHexDigit <* string "X")),
   string_prod = lexicalToken (char '"' *> takeWhile (/= "\"") <* char '"'
                               <|> char '\'' *> takeWhile (/= "'") <* char '\''),   -- Oberon2
   set = Set <$ delimiter "{" <*> sepBy element (delimiter ",") <* delimiter "}",
   element = Element <$> expression 
             <|> Range <$> expression <* delimiter ".." <*> expression,
   designator = Variable <$> qualident 
                <|> Field <$> designator <* delimiter "." <*> ident
                <|> Index <$> designator <* delimiter "[" <*> expList <* delimiter "]"
                <|> TypeGuard <$> designator <* delimiter "(" <*> qualident <* delimiter ")"
                <|> Dereference <$> designator <* operator "^",
   expList = sepByNonEmpty expression (delimiter ","),
   actualParameters = delimiter "(" *> sepBy expression (delimiter ",") <* delimiter ")",
   mulOperator = BinOp <$> (Multiply <$ operator "*" <|> Divide <$ operator "/"
                            <|> IntegerDivide <$ keyword "DIV" <|> Modulo <$ keyword "MOD" <|> And <$ operator "&"),
   addOperator = BinOp <$> (Add <$ operator "+" <|> Subtract <$ operator "-" <|> Or <$ keyword "OR"),
   relation = Equal <$ operator "=" <|> Unequal <$ operator "#" 
              <|> Less <$ operator "<" <|> LessOrEqual <$ operator "<=" 
              <|> Greater <$ operator ">" <|> GreaterOrEqual <$ operator ">=" 
              <|> In <$ keyword "IN" <|> Is <$ keyword "IS",
   typeDeclaration = TypeDeclaration <$> identdef <* delimiter "=" <*> type_prod,
   type_prod = TypeReference <$> qualident 
               <|> arrayType 
               <|> recordType 
               <|> pointerType 
               <|> procedureType,
   qualident = QualIdent <$> ident <* delimiter "." <*> ident 
               <|> NonQualIdent <$> ident,
   arrayType = ArrayType <$ keyword "ARRAY" <*> sepByNonEmpty length (delimiter ",") <* keyword "OF" <*> type_prod,
   length = constExpression,
   recordType = RecordType <$ keyword "RECORD" <*> optional (delimiter "(" *> baseType <* delimiter ")") 
                <*> fieldListSequence <* keyword "END",
   baseType = qualident,
   fieldListSequence = sepBy fieldList (delimiter ";"),
   fieldList = FieldList <$> identList <* delimiter ":" <*> type_prod,
   identList = sepByNonEmpty identdef (delimiter ","),
   pointerType = PointerType <$ keyword "POINTER" <* keyword "TO" <*> type_prod,
   procedureType = ProcedureType <$ keyword "PROCEDURE" <*> optional formalParameters,
   variableDeclaration = VariableDeclaration <$> identList <* delimiter ":" <*> type_prod,
   procedureDeclaration = ProcedureDeclaration <$> procedureHeading <* delimiter ";" <*> procedureBody <*> ident,
   procedureHeading = ProcedureHeading <$ keyword "PROCEDURE" <*> (True <$ delimiter "*" <|> pure False) 
                      <*> identdef <*> optional formalParameters,
   formalParameters = FormalParameters <$ delimiter "(" <*> sepBy fPSection (delimiter ";") <* delimiter ")" 
                      <*> optional (delimiter ":" *> qualident),
   fPSection = FPSection <$> (True <$ keyword "VAR" <|> pure False) 
               <*> sepByNonEmpty ident (delimiter ",") <* delimiter ":" <*> formalType,
   formalType = ArrayOf <$ keyword "ARRAY" <* keyword "OF" <*> formalType 
                <|> FormalTypeReference <$> qualident 
                <|> FormalProcedureType <$ keyword "PROCEDURE" <*> optional formalParameters,
   procedureBody = ProcedureBody <$> declarationSequence 
                   <*> optional (keyword "BEGIN" *> statementSequence) <* keyword "END",
   forwardDeclaration = ForwardDeclaration <$ keyword "PROCEDURE" <* delimiter "^"
                        <*> identdef <*> optional formalParameters,
   statementSequence = sepBy (ambiguous statement) (delimiter ";"),
   statement = assignment <|> procedureCall <|> ifStatement <|> caseStatement 
               <|> whileStatement <|> repeatStatement <|> forStatement <|> loopStatement <|> withStatement 
               <|> Exit <$ keyword "EXIT" 
               <|> Return <$ keyword "RETURN" <*> optional expression
               <|> pure EmptyStatement,
   assignment  =  Assignment <$> ambiguous designator <* delimiter ":=" <*> expression,
   procedureCall = ProcedureCall <$> ambiguous designator <*> optional actualParameters,
   ifStatement = If <$ keyword "IF"
       <*> sepByNonEmpty ((,) <$> expression <* keyword "THEN" <*> statementSequence) (keyword "ELSIF")
       <*> optional (keyword "ELSE" *> statementSequence) <* keyword "END",
   caseStatement = CaseStatement <$ keyword "CASE" <*> expression <* keyword "OF" <*> sepBy case_prod (skipSome $ delimiter "|")
       <*> optional (keyword "ELSE" *> statementSequence) <* keyword "END",
   case_prod  =  Case <$> caseLabelList <* delimiter ":" <*> statementSequence,
   caseLabelList  =  sepByNonEmpty caseLabels (delimiter ","),
   caseLabels = SingleLabel <$> constExpression 
                <|> LabelRange <$> constExpression <* delimiter ".." <*> constExpression,
   whileStatement = While <$ keyword "WHILE" <*> expression <* keyword "DO" <*> statementSequence <* keyword "END",
   repeatStatement = Repeat <$ keyword "REPEAT" <*> statementSequence <* keyword "UNTIL" <*> expression,
   forStatement = For <$ keyword "FOR" <*> ident <* delimiter ":=" <*> expression <* keyword "TO" <*> expression 
                  <*> optional (keyword "BY" *> constExpression) <* keyword "DO"
                  <*> statementSequence <* keyword "END", -- Oberon2
   loopStatement = Loop <$ keyword "LOOP" <*> statementSequence <* keyword "END",
   withStatement = With <$ keyword "WITH" <*> qualident <* delimiter ":" <*> qualident
                   <* keyword "DO" <*> statementSequence <* keyword "END"}

moptional p = p <|> mempty

delimiter, operator :: Text -> Parser (OberonGrammar f) Text Text

delimiter s = lexicalToken (string s)
operator = delimiter

reservedWords :: [Text]
reservedWords = ["ARRAY", "IMPORT", "RETURN",
                 "BEGIN", "IN", "THEN",
                 "BY", "IS", "TO",
                 "CASE", "LOOP", "TYPE",
                 "DIV", "MODULE", "VAR",
                 "DO", "NIL", "WHILE",
                 "ELSE", "OF", "WITH",
                 "ELSIF", "OR",
                 "END", "POINTER",
                 "EXIT", "PROCEDURE",
                 "FOR", "RECORD",
                 "IF", "REPEAT"]

{-
https://cseweb.ucsd.edu/~wgg/CSE131B/oberon2.htm

Module       = MODULE ident ";" [ImportList] DeclSeq
               [BEGIN StatementSeq] END ident ".".
ImportList   = IMPORT [ident ":="] ident {"," [ident ":="] ident} ";".
DeclSeq      = { CONST {ConstDecl ";" } | TYPE {TypeDecl ";"}
                 | VAR {VarDecl ";"}} {ProcDecl ";" | ForwardDecl ";"}.
ConstDecl    = IdentDef "=" ConstExpr.
TypeDecl     = IdentDef "=" Type.
VarDecl      = IdentList ":" Type.
ProcDecl     = PROCEDURE [Receiver] IdentDef [FormalPars] ";" DeclSeq
               [BEGIN StatementSeq] END ident.
ForwardDecl  = PROCEDURE "^" [Receiver] IdentDef [FormalPars].
FormalPars   = "(" [FPSection {";" FPSection}] ")" [":" Qualident].
FPSection    = [VAR] ident {"," ident} ":" Type.
Receiver     = "(" [VAR] ident ":" ident ")".
Type         = Qualident
             | ARRAY [ConstExpr {"," ConstExpr}] OF Type
             | RECORD ["("Qualident")"] FieldList {";" FieldList} END
             | POINTER TO Type
             | PROCEDURE [FormalPars].
FieldList    = [IdentList ":" Type].
StatementSeq = Statement {";" Statement}.
Statement    = [ Designator ":=" Expr 
             | Designator ["(" [ExprList] ")"] 
             | IF Expr THEN StatementSeq {ELSIF Expr THEN StatementSeq}
               [ELSE StatementSeq] END 
             | CASE Expr OF Case {"|" Case} [ELSE StatementSeq] END 
             | WHILE Expr DO StatementSeq END 
             | REPEAT StatementSeq UNTIL Expr 
             | FOR ident ":=" Expr TO Expr [BY ConstExpr] DO StatementSeq END 
             | LOOP StatementSeq END
             | WITH Guard DO StatementSeq {"|" Guard DO StatementSeq}
               [ELSE StatementSeq] END
             | EXIT 
             | RETURN [Expr]
             ].
Case         = [CaseLabels {"," CaseLabels} ":" StatementSeq].
CaseLabels   = ConstExpr [".." ConstExpr].
Guard        = Qualident ":" Qualident.
ConstExpr    = Expr.
Expr         = SimpleExpr [Relation SimpleExpr].
SimpleExpr   = ["+" | "-"] Term {AddOp Term}.
Term         = Factor {MulOp Factor}.
Factor       = Designator ["(" [ExprList] ")"] | number | character | string
               | NIL | Set | "(" Expr ")" | " ~ " Factor.
Set          = "{" [Element {"," Element}] "}".
Element      = Expr [".." Expr].
Relation     = "=" | "#" | "<" | "<=" | ">" | ">=" | IN | IS.
AddOp        = "+" | "-" | OR.
MulOp        = " * " | "/" | DIV | MOD | "&".
Designator   = Qualident {"." ident | "[" ExprList "]" | " ^ "
               | "(" Qualident ")"}.
ExprList     = Expr {"," Expr}.
IdentList    = IdentDef {"," IdentDef}.
Qualident    = [ident "."] ident.
IdentDef     = ident [" * " | "-"].
-}

{-
EBNF definition of a Module Definition ( .Def)

A module definition follows the Oberon grammar. The only differences are in the productions:

module  =  DEFINITION ident ";"  [ImportList] DeclarationSequence END ident ".".

where the body is removed and in:

ProcedureDeclaration  = ProcedureHeading ";"

where ProcedureBody and ident are removed. All the productions from ProcedureBody may be ignored. Depending on the tool (Watson or Browser), the export marks may or may not be included in the output.

12 Jul 2002 - Copyright © 2002 ETH Zürich. All rights reserved.
E-Mail: oberon-web at inf.ethz.ch
Homepage: www.ethoberon.ethz.ch {http://www.ethoberon.ethz.ch/}
-}
