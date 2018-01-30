{-# Language OverloadedStrings, Rank2Types, RecordWildCards, TemplateHaskell #-}

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

import qualified Rank2
import qualified Rank2.TH

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

$(Rank2.TH.deriveAll ''OberonGrammar)

oberonGrammar :: Grammar OberonGrammar Parser Text
oberonGrammar = fixGrammar grammar

grammar :: GrammarBuilder OberonGrammar OberonGrammar Parser Text
grammar OberonGrammar{..} = OberonGrammar{
   module_prod = Module <$ (ignorable *> keyword "MODULE") <*> ident <* delimiter ";"
                 <*> moptional importList <*> declarationSequence
                 <*> optional (keyword "BEGIN" *> statementSequence) <* keyword "END" <*> ident <* delimiter ".",
   ident = letter <> takeCharsWhile isAlphaNum <* ignorable,
   letter = satisfyCharInput isLetter,
   digit = satisfyCharInput isDigit,
   importList = keyword "IMPORT" *> sepBy1 import_prod (delimiter ",") <* delimiter ";",
   import_prod = Import <$> ident <*> optional (delimiter ":=" *> ident),
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
                      <*> (term <**> (pure id <|> flip <$> addOperator <*> term)),
   term = factor <**> (pure id <|> flip <$> mulOperator <*> term),
   factor  =  number
              <|> charConstant
              <|> String <$> string_prod
              <|> Nil <$ keyword "NIL"
              <|> BooleanConstant <$> (True <$ keyword "TRUE" <|> False <$ keyword "FALSE")
              <|> set
              <|> Read <$> designator
              <|> FunctionCall <$> designator <*> actualParameters
              <|> delimiter "(" *> expression <* delimiter ")"
              <|> Not <$ operator "~" <*> factor,
   number  =  integer <|> real,
   integer = Integer <$> (digit <> (takeCharsWhile isDigit <|> takeCharsWhile isHexDigit <> string "H") <* ignorable),
   hexDigit = satisfyCharInput isHexDigit,
   real = Real <$> (digit <> takeCharsWhile isDigit <> string "." *> takeCharsWhile isDigit <> moptional scaleFactor
                    <* ignorable),
   scaleFactor = (string "E" <|> string "D") <> moptional (string "+" <|> string "-") <> digit <> takeCharsWhile isDigit,
   charConstant = (CharConstant <$ char '"' <*> anyChar <* char '"'
                   <|> (CharCode . fst . head . readHex . unpack) <$> (digit <> takeCharsWhile isHexDigit)
                   <* string "X") <* ignorable,
   string_prod = char '"' *> takeWhile (/= "\"") <* char '"' <* ignorable,
   set = Set <$ delimiter "{" <*> sepBy element (delimiter ",") <* delimiter "}",
   element = Element <$> expression 
             <|> Range <$> expression <* delimiter ".." <*> expression,
   designator = Variable <$> qualident 
                <|> Field <$> designator <* delimiter "." <*> ident
                <|> Index <$> designator <* delimiter "[" <*> expList <* delimiter "]"
                <|> TypeGuard <$> designator <* delimiter "(" <*> qualident <* delimiter ")"
                <|> Dereference <$> designator <* operator "^",
   expList = sepBy1' expression (delimiter ","),
   actualParameters = delimiter "(" *> sepBy expression (delimiter ",") <* delimiter ")",
   mulOperator = Multiply <$ operator "*" <|> Divide <$ operator "/" 
                 <|> IntegerDivide <$ keyword "DIV" <|> Modulo <$ keyword "MOD" <|> And <$ operator "&",
   addOperator = Add <$ operator "+" <|> Subtract <$ operator "-" <|> Or <$ keyword "OR",
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
   arrayType = ArrayType <$ keyword "ARRAY" <*> sepBy1' length (delimiter ",") <* keyword "OF" <*> type_prod,
   length = constExpression,
   recordType = RecordType <$ keyword "RECORD" <*> optional (delimiter "(" *> baseType <* delimiter ")") 
                <*> fieldListSequence <* keyword "END",
   baseType = qualident,
   fieldListSequence = sepBy fieldList (delimiter ";"),
   fieldList = FieldList <$> identList <* delimiter ":" <*> type_prod,
   identList = sepBy1' identdef (delimiter ","),
   pointerType = PointerType <$ keyword "POINTER" <* keyword "TO" <*> type_prod,
   procedureType = ProcedureType <$ keyword "PROCEDURE" <*> optional formalParameters,
   variableDeclaration = VariableDeclaration <$> identList <* delimiter ":" <*> type_prod,
   procedureDeclaration = ProcedureDeclaration <$> procedureHeading <* delimiter ";" <*> procedureBody <*> ident,
   procedureHeading = ProcedureHeading <$ keyword "PROCEDURE" <*> (True <$ delimiter "*" <|> pure False) 
                      <*> identdef <*> optional formalParameters,
   formalParameters = FormalParameters <$ delimiter "(" <*> sepBy fPSection (delimiter ";") <* delimiter ")" 
                      <*> optional (delimiter ":" *> qualident),
   fPSection = FPSection <$> (True <$ keyword "VAR" <|> pure False) 
               <*> sepBy1' ident (delimiter ",") <* delimiter ":" <*> formalType,
   formalType = ArrayOf <$ keyword "ARRAY" <* keyword "OF" <*> formalType 
                <|> FormalTypeReference <$> qualident 
                <|> FormalProcedureType <$ keyword "PROCEDURE" <*> optional formalParameters,
   procedureBody = ProcedureBody <$> declarationSequence 
                   <*> optional (keyword "BEGIN" *> statementSequence) <* keyword "END",
   forwardDeclaration = ForwardDeclaration <$ keyword "PROCEDURE" <* delimiter "^" <*> ident 
                        <*> (True <$ delimiter "*" <|> pure False) <*> optional formalParameters,
   statementSequence = sepBy statement (delimiter ";"),
   statement = assignment <|> procedureCall <|> ifStatement <|> caseStatement 
               <|> whileStatement <|> repeatStatement <|> loopStatement <|> withStatement 
               <|> Exit <$ keyword "EXIT" 
               <|> Return <$ keyword "RETURN" <*> optional expression,
   assignment  =  Assignment <$> designator <* delimiter ":=" <*> expression,
   procedureCall = ProcedureCall <$> designator <*> optional actualParameters,
   ifStatement = If <$ keyword "IF" <*> expression <* keyword "THEN" <*> statementSequence
       <*> many ((,) <$ keyword "ELSIF" <*> expression <* keyword "THEN" <*> statementSequence)
       <*> optional (keyword "ELSE" *> statementSequence) <* keyword "END",
   caseStatement = CaseStatement <$ keyword "CASE" <*> expression <* keyword "OF" <*> sepBy1' case_prod (delimiter "|") 
       <*> optional (keyword "ELSE" *> statementSequence) <* keyword "END",
   case_prod  =  optional (Case <$> caseLabelList <* delimiter ":" <*> statementSequence),
   caseLabelList  =  sepBy1' caseLabels (delimiter ","),
   caseLabels = SingleLabel <$> constExpression 
                <|> LabelRange <$> constExpression <* delimiter ".." <*> constExpression,
   whileStatement = While <$ keyword "WHILE" <*> expression <* keyword "DO" <*> statementSequence <* keyword "END",
   repeatStatement = Repeat <$ keyword "REPEAT" <*> statementSequence <* keyword "UNTIL" <*> expression,
   loopStatement = Loop <$ keyword "LOOP" <*> statementSequence <* keyword "END",
   withStatement = With <$ keyword "WITH" <*> qualident <* delimiter ":" <*> qualident
                   <* keyword "DO" <*> statementSequence <* keyword "END"}

sepBy1' p q = fromList <$> sepBy1 p q

moptional p = p <|> mempty

keyword, delimiter, operator :: Text -> Parser OberonGrammar Text Text

keyword s = string s <* notSatisfyChar isAlphaNum <* ignorable
delimiter s = string s <* ignorable
operator = delimiter

ignorable :: Parser OberonGrammar Text ()
ignorable = whiteSpace
            *> skipMany (string "(*" *> skipMany (notFollowedBy (string "*)") *> anyToken *> takeCharsWhile (/= '*'))
                         *> string "*)" *> whiteSpace)

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
