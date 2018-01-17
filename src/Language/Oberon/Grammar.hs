{-# Language OverloadedStrings, Rank2Types, RecordWildCards #-}

-- * From http://www.ethoberon.ethz.ch/EBNF.html
--   Extracted from the book Programmieren in Oberon - Das neue Pascal by N. Wirth and M. Reiser and translated by J. Templ.

module Language.Oberon.Grammar where

import Control.Applicative
import Data.Char
import Data.List.NonEmpty (NonEmpty((:|)), fromList, toList)
import Data.Monoid ((<>))
import Numeric (readHex)
import Data.Text (Text, unpack)
import Text.Grampa
import Text.Grampa.ContextFree.LeftRecursive (Parser)
import Text.Parser.Combinators (sepBy, sepBy1)

import Language.Oberon.AST

import Prelude hiding (length, takeWhile)

data OberonGrammar f = OberonGrammar {
   module_prod :: f Module,
   ident :: f Ident,
   letter :: f Text,
   digit :: f Text,
   importList :: f [Import],
   import_prod :: f Import,
   declarationSequence :: f [Declaration],
   constantDeclaration :: f Declaration,
   identdef :: f IdentDef,
   constExpression :: f Expression,
   expression :: f Expression,
   simpleExpression :: f Expression,
   term :: f Expression,
   factor :: f Expression,
   number :: f Expression,
   integer :: f Expression,
   hexDigit :: f Text,
   real :: f Expression,
   scaleFactor :: f Text,
   charConstant :: f Expression,
   string_prod :: f Text,
   set :: f Expression,
   element :: f Element,
   designator :: f Designator,
   expList :: f (NonEmpty Expression),
   actualParameters :: f [Expression],
   mulOperator :: f (Expression -> Expression -> Expression),
   addOperator :: f (Expression -> Expression -> Expression),
   relation :: f RelOp,
   typeDeclaration :: f Declaration,
   type_prod :: f Type,
   qualident :: f QualIdent,
   arrayType :: f Type,
   length :: f Expression,
   recordType :: f Type,
   baseType :: f QualIdent,
   fieldListSequence :: f FieldListSequence,
   fieldList :: f FieldList,
   identList :: f IdentList,
   pointerType :: f Type,
   procedureType :: f Type,
   variableDeclaration :: f Declaration,
   procedureDeclaration :: f Declaration,
   procedureHeading :: f ProcedureHeading,
   formalParameters :: f FormalParameters,
   fPSection :: f FPSection,
   formalType :: f FormalType,
   procedureBody :: f ProcedureBody,
   forwardDeclaration :: f Declaration,
   statementSequence :: f [Statement],
   statement :: f Statement,
   assignment :: f Statement,
   procedureCall :: f Statement,
   ifStatement :: f Statement,
   caseStatement :: f Statement,
   case_prod :: f (Maybe Case),
   caseLabelList :: f (NonEmpty CaseLabels),
   caseLabels :: f CaseLabels,
   whileStatement :: f Statement,
   repeatStatement :: f Statement,
   loopStatement :: f Statement,
   withStatement :: f Statement}

grammar :: GrammarBuilder OberonGrammar OberonGrammar Parser Text
grammar OberonGrammar{..} = OberonGrammar{
   module_prod = Module <$ string "MODULE" <*> ident <* string ";"
                 <*> moptional importList <*> declarationSequence
                 <*> optional (string "BEGIN" *> statementSequence) <* string "END" <*> ident <* string ".",
   ident = letter <> takeCharsWhile isAlphaNum,
   letter = satisfyCharInput isLetter,
   digit = satisfyCharInput isDigit,
   importList = string "IMPORT" *> sepBy1 import_prod (string ",") <* string ";",
   import_prod = Import <$> ident <*> optional (string ":=" *> ident),
   declarationSequence = concatMany (string "CONST" *> many (constantDeclaration <* string ";")
                                     <|> string "TYPE" *> many (typeDeclaration <* string ";")
                                     <|> string "VAR" *> many (variableDeclaration <* string ";"))
                         <> many (procedureDeclaration <* string ";"
                                  <|> forwardDeclaration <* string ";"),
   constantDeclaration = ConstantDeclaration <$> identdef <* string "=" <*> constExpression,
   identdef = IdentDef <$> ident <*> (True <$ string "*" <|> pure False),
   constExpression = expression,
   expression = simpleExpression <**> (pure id <|> (flip . Relation) <$> relation <*> simpleExpression),
   simpleExpression = (Positive <$ string "+" <|> Negative <$ string "-" <|> pure id)
                      <*> (term <**> (pure id <|> flip <$> addOperator <*> term)),
   term = factor <**> (pure id <|> flip <$> mulOperator <*> term),
   factor  =  number
              <|> charConstant
              <|> String <$> string_prod
              <|> Nil <$ string "NIL"
              <|> set
              <|> Read <$> designator
              <|> FunctionCall <$> designator <*> actualParameters
              <|> string "(" *> expression <* string ")"
              <|> Negate <$ string "~" <*> factor,
   number  =  integer <|> real,
   integer = Integer <$> (digit <> (takeCharsWhile isDigit <|> takeCharsWhile isHexDigit <> string "H")),
   hexDigit = satisfyCharInput isHexDigit,
   real = Real <$> (digit <> takeCharsWhile isDigit <> string "." *> takeCharsWhile isDigit <> moptional scaleFactor),
   scaleFactor = (string "E" <|> string "D") <> moptional (string "+" <|> string "-") <> digit <> takeCharsWhile isDigit,
   charConstant = CharConstant <$ char '"' <*> anyChar <* char '"'
                  <|> (CharCode . fst . head . readHex . unpack) <$> (digit <> takeCharsWhile isHexDigit) <* string "X",
   string_prod = char '"' *> takeWhile (/= "\"") <* char '"',
   set = Set <$ string "{" <*> sepBy element (string ",") <* string "}",
   element = Element <$> expression 
             <|> Range <$> expression <* string ".." <*> expression,
   designator = Variable <$> qualident 
                <|> Field <$> designator <*> ident
                <|> Index <$> designator <* string "[" <*> expList <* string "]"
                <|> TypeGuard <$> designator <* string "(" <*> qualident <* string ")"
                <|> Dereference <$> designator <* string "^",
   expList = sepBy1' expression (string ","),
   actualParameters = string "(" *> sepBy expression (string ",") <* string ")",
   mulOperator = Multiply <$ string "*" <|> Divide <$ string "/" 
                 <|> IntegerDivide <$ string "DIV" <|> Modulo <$ string "MOD" <|> And <$ string "&",
   addOperator = Add <$ string "+" <|> Subtract <$ string "-" <|> Or <$ string "OR",
   relation = Equal <$ string "=" <|> Unequal <$ string "#" 
              <|> Less <$ string "<" <|> LessOrEqual <$ string "<=" 
              <|> Greater <$ string ">" <|> GreaterOrEqual <$ string ">=" 
              <|> In <$ string "IN" <|> Is <$ string "IS",
   typeDeclaration = TypeDeclaration <$> identdef <* string "=" <*> type_prod,
   type_prod = TypeReference <$> qualident 
               <|> arrayType 
               <|> recordType 
               <|> pointerType 
               <|> procedureType,
   qualident = QualIdent <$> ident <* string "." <*> ident 
               <|> NonQualIdent <$> ident,
   arrayType = ArrayType <$ string "ARRAY" <*> sepBy1' length (string ",") <* string "OF" <*> type_prod,
   length = constExpression,
   recordType = RecordType <$ string "RECORD" <*> optional (string "(" *> baseType <* string ")") 
                <*> fieldListSequence <* string "END",
   baseType = qualident,
   fieldListSequence = sepBy fieldList (string ";"),
   fieldList = FieldList <$> identList <* string ":" <*> type_prod,
   identList = sepBy1' identdef (string ","),
   pointerType = PointerType <$ string "POINTER" <* string "TO" <*> type_prod,
   procedureType = ProcedureType <$ string "PROCEDURE" <*> optional formalParameters,
   variableDeclaration = VariableDeclaration <$> identList <* string ":" <*> type_prod,
   procedureDeclaration = ProcedureDeclaration <$> procedureHeading <* string ";" <*> procedureBody <*> ident,
   procedureHeading = ProcedureHeading <$ string "PROCEDURE" <*> (True <$ string "*" <|> pure False) 
                      <*> identdef <*> optional formalParameters,
   formalParameters = FormalParameters <$ string "(" <*> sepBy fPSection (string ";") <* string ")" 
                      <*> optional (string ":" *> qualident),
   fPSection = FPSection <$> (True <$ string "VAR" <|> pure False) 
               <*> sepBy1' ident (string ",") <* string ":" <*> formalType,
   formalType = ArrayOf <$ string "ARRAY" <* string "OF" <*> formalType 
                <|> FormalTypeReference <$> qualident 
                <|> FormalProcedureType <$ string "PROCEDURE" <*> optional formalParameters,
   procedureBody = ProcedureBody <$> declarationSequence 
                   <*> optional (string "BEGIN" *> statementSequence) <* string "END",
   forwardDeclaration = ForwardDeclaration <$ string "PROCEDURE" <* string "^" <*> ident 
                        <*> (True <$ string "*" <|> pure False) <*> optional formalParameters,
   statementSequence = sepBy statement (string ";"),
   statement = assignment <|> procedureCall <|> ifStatement <|> caseStatement 
               <|> whileStatement <|> repeatStatement <|> loopStatement <|> withStatement 
               <|> Exit <$ string "EXIT" 
               <|> Return <$ string "RETURN" <*> optional expression,
   assignment  =  Assignment <$> designator <* string ":=" <*> expression,
   procedureCall = ProcedureCall <$> designator <*> optional actualParameters,
   ifStatement = If <$ string "IF" <*> expression <* string "THEN" <*> statementSequence
       <*> many ((,) <$ string "ELSIF" <*> expression <* string "THEN" <*> statementSequence)
       <*> optional (string "ELSE" *> statementSequence) <* string "END",
   caseStatement = CaseStatement <$ string "CASE" <*> expression <* string "OF" <*> sepBy1' case_prod (string "|") 
       <*> optional (string "ELSE" *> statementSequence) <* string "END",
   case_prod  =  optional (Case <$> caseLabelList <* string ":" <*> statementSequence),
   caseLabelList  =  sepBy1' caseLabels (string ","),
   caseLabels = SingleLabel <$> constExpression 
                <|> LabelRange <$> constExpression <* string ".." <*> constExpression,
   whileStatement = While <$ string "WHILE" <*> expression <* string "DO" <*> statementSequence <* string "END",
   repeatStatement = Repeat <$ string "REPEAT" <*> statementSequence <* string "UNTIL" <*> expression,
   loopStatement = Loop <$ string "LOOP" <*> statementSequence <* string "END",
   withStatement = With <$ string "WITH" <*> qualident <* string ":" <*> qualident
                   <* string "DO" <*> statementSequence <* string "END"}

sepBy1' p q = fromList <$> sepBy1 p q

moptional p = p <|> mempty

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
