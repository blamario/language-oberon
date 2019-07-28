{-# Language OverloadedStrings, Rank2Types, RecordWildCards, ScopedTypeVariables, TypeFamilies, TemplateHaskell #-}

-- | Oberon grammar adapted from http://www.ethoberon.ethz.ch/EBNF.html
-- Extracted from the book Programmieren in Oberon - Das neue Pascal by N. Wirth and M. Reiser and translated by J. Templ.

module Language.Oberon.Grammar (OberonGrammar(..), NodeWrap,
                                oberonGrammar, oberon2Grammar, oberonDefinitionGrammar, oberon2DefinitionGrammar) where

import Control.Applicative
import Control.Monad (guard)
import Data.Char
import Data.Functor.Compose (Compose(..))
import Data.List.NonEmpty (NonEmpty((:|)), fromList, toList)
import Data.Monoid ((<>), Endo(Endo, appEndo))
import Numeric (readDec, readHex, readFloat)
import Data.Text (Text, unpack)
import Text.Grampa
import Text.Grampa.ContextFree.LeftRecursive (Parser)
import Text.Parser.Combinators (sepBy, sepBy1, sepByNonEmpty, try)
import Text.Parser.Token (braces, brackets, parens)

import Transformation.Deep as Deep (Product(Pair))
import qualified Rank2
import qualified Rank2.TH

import qualified Language.Oberon.Abstract as Abstract
import qualified Language.Oberon.AST as AST

import Prelude hiding (length, takeWhile)

-- | All the productions of the Oberon grammar
data OberonGrammar l f p = OberonGrammar {
   module_prod :: p (Abstract.Module l l f f),
   ident :: p Abstract.Ident,
   letter :: p Text,
   digit :: p Text,
   importList :: p [Abstract.Import l],
   import_prod :: p (Abstract.Import l),
   declarationSequence :: p [f (Abstract.Declaration l l f f)],
   constantDeclaration :: p (Abstract.Declaration l l f f),
   identdef :: p (Abstract.IdentDef l),
   constExpression :: p (f (Abstract.Expression l l f f)),
   expression :: p (f (Abstract.Expression l l f f)),
   simpleExpression :: p (f (Abstract.Expression l l f f)),
   term :: p (f (Abstract.Expression l l f f)),
   factor :: p (f (Abstract.Expression l l f f)),
   number :: p (Abstract.Expression l l f f),
   integer :: p (Abstract.Expression l l f f),
   hexDigit :: p Text,
   real :: p (Abstract.Expression l l f f),
   scaleFactor :: p Text,
   charConstant :: p (Abstract.Expression l l f f),
   string_prod :: p Text,
   set :: p (Abstract.Expression l l f f),
   element :: p (Abstract.Element l l f f),
   designator :: p (f (Abstract.Designator l l f f)),
   expList :: p (NonEmpty (f (Abstract.Expression l l f f))),
   actualParameters :: p [f (Abstract.Expression l l f f)],
   mulOperator :: p (BinOp l f),
   addOperator :: p (BinOp l f),
   relation :: p Abstract.RelOp,
   typeDeclaration :: p (Abstract.Declaration l l f f),
   type_prod :: p (Abstract.Type l l f f),
   qualident :: p (Abstract.QualIdent l),
   arrayType :: p (Abstract.Type l l f f),
   length :: p (f (Abstract.Expression l l f f)),
   recordType :: p (Abstract.Type l l f f),
   baseType :: p (Abstract.BaseType l),
   fieldListSequence :: p (NonEmpty (f (Abstract.FieldList l l f f))),
   fieldList :: p (Abstract.FieldList l l f f),
   identList :: p (Abstract.IdentList l),
   pointerType :: p (Abstract.Type l l f f),
   procedureType :: p (Abstract.Type l l f f),
   variableDeclaration :: p (Abstract.Declaration l l f f),
   procedureDeclaration :: p (Abstract.Declaration l l f f),
   procedureHeading :: p (Abstract.Ident, Abstract.ProcedureHeading l l f f),
   formalParameters :: p (Abstract.FormalParameters l l f f),
   fPSection :: p (Abstract.FPSection l l f f),
   formalType :: p (Abstract.Type l l f f),
   procedureBody :: p (Abstract.Block l l f f),
   forwardDeclaration :: p (Abstract.Declaration l l f f),
   statementSequence :: p (Abstract.StatementSequence l l f f),
   statement :: p (Abstract.Statement l l f f),
   assignment :: p (Abstract.Statement l l f f),
   procedureCall :: p (Abstract.Statement l l f f),
   ifStatement :: p (Abstract.Statement l l f f),
   caseStatement :: p (Abstract.Statement l l f f),
   case_prod :: p (Abstract.Case l l f f),
   caseLabelList :: p (NonEmpty (f (Abstract.CaseLabels l l f f))),
   caseLabels :: p (Abstract.CaseLabels l l f f),
   whileStatement :: p (Abstract.Statement l l f f),
   repeatStatement :: p (Abstract.Statement l l f f),
   forStatement :: p (Abstract.Statement l l f f),
   loopStatement :: p (Abstract.Statement l l f f),
   withStatement :: p (Abstract.Statement l l f f)}

newtype BinOp l f = BinOp {applyBinOp :: (f (Abstract.Expression l l f f)
                                          -> f (Abstract.Expression l l f f)
                                          -> f (Abstract.Expression l l f f))}

instance Show (BinOp l f) where
   show = const "BinOp{}"

$(Rank2.TH.deriveAll ''OberonGrammar)

instance Lexical (OberonGrammar l f) where
   type LexicalConstraint p (OberonGrammar l f) s = (s ~ Text, p ~ Parser)
   lexicalComment = try (string "(*"
                         *> skipMany (lexicalComment
                                      <|> notFollowedBy (string "*)") <* anyToken <* takeCharsWhile isCommentChar)
                         <* string "*)")
      where isCommentChar c = c /= '*' && c /= '('
   lexicalWhiteSpace = takeCharsWhile isSpace *> skipMany (lexicalComment *> takeCharsWhile isSpace)
   isIdentifierStartChar = isLetter
   isIdentifierFollowChar = isAlphaNum
   identifierToken word = lexicalToken (do w <- word
                                           guard (w `notElem` reservedWords)
                                           return w)

type NodeWrap = Compose ((,) (Position Text)) Ambiguous

oberonGrammar, oberon2Grammar, oberonDefinitionGrammar, oberon2DefinitionGrammar
   :: Grammar (OberonGrammar AST.Language NodeWrap) Parser Text
-- | Grammar of an Oberon module
oberonGrammar = fixGrammar grammar
-- | Grammar of an Oberon-2 module
oberon2Grammar = fixGrammar grammar2
-- | Grammar of an Oberon definition module
oberonDefinitionGrammar = fixGrammar definitionGrammar
-- | Grammar of an Oberon-2 definition module
oberon2DefinitionGrammar = fixGrammar definitionGrammar2

grammar, definitionGrammar :: forall l. Abstract.Oberon l
                           => GrammarBuilder (OberonGrammar l NodeWrap) (OberonGrammar l NodeWrap) Parser Text
grammar2, definitionGrammar2 :: forall l. Abstract.Oberon2 l
                             => GrammarBuilder (OberonGrammar l NodeWrap) (OberonGrammar l NodeWrap) Parser Text

definitionGrammar g@OberonGrammar{..} = definitionMixin (grammar g)

definitionGrammar2 g@OberonGrammar{..} = definitionMixin (grammar2 g)

definitionMixin :: Abstract.Oberon l => GrammarBuilder (OberonGrammar l NodeWrap) (OberonGrammar l NodeWrap) Parser Text
definitionMixin g@OberonGrammar{..} = g{
   module_prod = do lexicalWhiteSpace 
                    keyword "DEFINITION"
                    name <- ident
                    delimiter ";"
                    imports <- moptional importList
                    declarations <- declarationSequence
                    keyword "END"
                    lexicalToken (string name)
                    delimiter "."
                    return (Abstract.moduleUnit name imports declarations Nothing),
   procedureDeclaration = Abstract.procedureDeclaration . snd . sequenceA 
                          <$> wrap procedureHeading 
                          <*> wrap (pure $ Abstract.block [] Nothing),
   identdef = Abstract.exported <$> ident <* optional (delimiter "*")}

grammar2 g@OberonGrammar{..} = g1{
   identdef = ident 
              <**> (Abstract.exported <$ delimiter "*" 
                    <|> Abstract.readOnly <$ delimiter "-" 
                    <|> pure Abstract.identDef),
   
   string_prod = string_prod1 <|> lexicalToken (char '\'' *> takeWhile (/= "'") <* char '\''),
   procedureHeading = procedureHeading1
                      <|> Abstract.typeBoundHeading <$ keyword "PROCEDURE"
                          <* delimiter "("
                          <*> (True <$ keyword "VAR" <|> pure False)
                          <*> ident
                          <* delimiter ":"
                          <*> ident
                          <* delimiter ")"
                          <*> (True <$ delimiter "*" <|> pure False)
                          <**> do n <- lookAhead ident
                                  idd <- identdef
                                  params <- optional (wrap formalParameters)
                                  pure (\proc-> (n, proc idd params)),
   arrayType =
      Abstract.arrayType <$ keyword "ARRAY" <*> sepBy length (delimiter ",") <* keyword "OF" <*> wrap type_prod,
   forStatement = 
      Abstract.forStatement <$ keyword "FOR" <*> ident <* delimiter ":=" <*> expression <* keyword "TO" <*> expression
      <*> optional (keyword "BY" *> constExpression) <* keyword "DO"
      <*> wrap statementSequence <* keyword "END",
   withStatement = Abstract.variantWithStatement <$ keyword "WITH"
                      <*> sepByNonEmpty (wrap withAlternative) (delimiter "|")
                      <*> optional (keyword "ELSE" *> wrap statementSequence) <* keyword "END"}
   where g1@OberonGrammar{string_prod= string_prod1, procedureHeading= procedureHeading1} = grammar g
         withAlternative = Abstract.withAlternative <$> qualident <* delimiter ":" <*> qualident
                                                    <*  keyword "DO" <*> wrap statementSequence

grammar OberonGrammar{..} = OberonGrammar{
   module_prod = do lexicalWhiteSpace
                    keyword "MODULE"
                    name <- ident
                    delimiter ";"
                    imports <- moptional importList
                    declarations <- declarationSequence
                    body <- optional (keyword "BEGIN" *> wrap statementSequence)
                    keyword "END"
                    lexicalToken (string name)
                    delimiter "."
                    return (Abstract.moduleUnit name imports declarations body),
   ident = identifier,
   letter = satisfyCharInput isLetter,
   digit = satisfyCharInput isDigit,
   importList = keyword "IMPORT" *> sepBy1 import_prod (delimiter ",") <* delimiter ";",
   import_prod = Abstract.moduleImport <$> optional (ident <* delimiter ":=") <*> ident,
   declarationSequence = concatMany (keyword "CONST" *> many (wrap constantDeclaration <* delimiter ";")
                                     <|> keyword "TYPE" *> many (wrap typeDeclaration <* delimiter ";")
                                     <|> keyword "VAR" *> many (wrap variableDeclaration <* delimiter ";"))
                         <> many (wrap procedureDeclaration <* delimiter ";"
                                  <|> wrap forwardDeclaration <* delimiter ";")
                         <?> "declarations",
   constantDeclaration = Abstract.constantDeclaration <$> identdef <* delimiter "=" <*> constExpression,
   identdef = ident <**> (Abstract.exported <$ delimiter "*" <|> pure Abstract.identDef),
   constExpression = expression,
   expression = simpleExpression
                <|> wrap (flip Abstract.relation <$> simpleExpression <*> relation <*> simpleExpression)
                <|> wrap (Abstract.is <$> simpleExpression <* keyword "IS" <*> qualident)
                <?> "expression",
   simpleExpression = 
      (wrap (Abstract.positive <$ operator "+" <*> term) <|> wrap (Abstract.negative <$ operator "-" <*> term :: Parser (OberonGrammar l NodeWrap) Text (Abstract.Expression l l NodeWrap NodeWrap)) <|> term)
      <**> (appEndo <$> concatMany (Endo <$> (flip . applyBinOp <$> addOperator <*> term))),
   term = factor <**> (appEndo <$> concatMany (Endo <$> (flip . applyBinOp <$> mulOperator <*> factor))),
   factor = wrapAmbiguous (number
                           <|> charConstant
                           <|> Abstract.literal <$> wrap (Abstract.string <$> string_prod)
                           <|> Abstract.literal <$> wrap (Abstract.nil <$ keyword "NIL")
                           <|> set
                           <|> Abstract.read <$> designator
                           <|> Abstract.functionCall <$> designator <*> actualParameters
                           <|> (Abstract.not <$ operator "~" <*> factor :: Parser (OberonGrammar l NodeWrap) Text (Abstract.Expression l l NodeWrap NodeWrap)))
            <|> parens expression,
   number  =  integer <|> real,
   integer = Abstract.literal
             <$> wrap (Abstract.integer . fst . head
                       <$> lexicalToken (readDec . unpack <$> takeCharsWhile1 isDigit
                                         <|> readHex . unpack <$> (digit <> takeCharsWhile isHexDigit <* string "H"))),
   hexDigit = satisfyCharInput isHexDigit,
   real = Abstract.literal
             <$> wrap (Abstract.real . fst . head . readFloat . unpack
                       <$> lexicalToken (takeCharsWhile1 isDigit <> string "." <> takeCharsWhile isDigit <> moptional scaleFactor)),
   scaleFactor = (string "E" <|> "E" <$ string "D") <> moptional (string "+" <|> string "-") <> takeCharsWhile1 isDigit,
   charConstant = Abstract.literal <$> wrap (lexicalToken (Abstract.charCode . fst . head . readHex . unpack
                                                           <$> (digit <> takeCharsWhile isHexDigit <* string "X"))),
   string_prod = lexicalToken (char '"' *> takeWhile (/= "\"") <* char '"'),
   set = Abstract.set <$> braces (sepBy (wrap element) (delimiter ",")),
   element = Abstract.element <$> expression
             <|> Abstract.range <$> expression <* delimiter ".." <*> expression,
   designator = wrapAmbiguous $
                    Abstract.variable <$> qualident
                <|> Abstract.field <$> designator <* delimiter "." <*> ident
                <|> Abstract.index <$> designator <*> brackets expList
                <|> Abstract.typeGuard <$> designator <*> parens qualident
                <|> Abstract.dereference <$> designator <* operator "^",
   expList = sepByNonEmpty expression (delimiter ","),
   actualParameters = parens (sepBy expression (delimiter ",")),
   mulOperator = BinOp . wrapBinary
                 <$> (Abstract.multiply <$ operator "*" <|> Abstract.divide <$ operator "/"
                      <|> Abstract.integerDivide <$ keyword "DIV" <|> Abstract.modulo <$ keyword "MOD" 
                      <|> Abstract.and <$ operator "&"),
   addOperator = BinOp . wrapBinary 
                 <$> (Abstract.add <$ operator "+" <|> Abstract.subtract <$ operator "-" 
                      <|> Abstract.or <$ keyword "OR"),
   relation = Abstract.Equal <$ operator "=" <|> Abstract.Unequal <$ operator "#" 
              <|> Abstract.Less <$ operator "<" <|> Abstract.LessOrEqual <$ operator "<=" 
              <|> Abstract.Greater <$ operator ">" <|> Abstract.GreaterOrEqual <$ operator ">=" 
              <|> Abstract.In <$ keyword "IN",
   typeDeclaration = Abstract.typeDeclaration <$> identdef <* delimiter "=" <*> wrap type_prod,
   type_prod = Abstract.typeReference <$> qualident 
               <|> arrayType 
               <|> recordType 
               <|> pointerType 
               <|> procedureType,
   qualident = Abstract.qualIdent <$> ident <* delimiter "." <*> ident
               <|> Abstract.nonQualIdent <$> ident,
   arrayType = Abstract.arrayType <$ keyword "ARRAY" <*> sepBy1 length (delimiter ",") <* keyword "OF" <*> wrap type_prod,
   length = constExpression,
   recordType = Abstract.recordType <$ keyword "RECORD" <*> optional (parens baseType)
                <*> fieldListSequence <* keyword "END",
   baseType = qualident,
   fieldListSequence = sepByNonEmpty (wrap fieldList) (delimiter ";"),
   fieldList = (Abstract.fieldList <$> identList <* delimiter ":" <*> wrap type_prod <?> "record field declarations")
               <|> pure Abstract.emptyFieldList,
   identList = sepByNonEmpty identdef (delimiter ","),
   pointerType = Abstract.pointerType <$ keyword "POINTER" <* keyword "TO" <*> wrap type_prod,
   procedureType = Abstract.procedureType <$ keyword "PROCEDURE" <*> optional (wrap formalParameters),
   variableDeclaration = Abstract.variableDeclaration <$> identList <* delimiter ":" <*> wrap type_prod,
   procedureDeclaration = do (procedureName, heading) <- sequenceA <$> wrap procedureHeading
                             delimiter ";"
                             body <- wrap procedureBody
                             lexicalToken (string procedureName)
                             return (Abstract.procedureDeclaration heading body),
   procedureHeading = Abstract.procedureHeading <$ keyword "PROCEDURE" <*> (True <$ delimiter "*" <|> pure False)
                      <**> do n <- lookAhead ident
                              idd <- identdef
                              params <- optional (wrap formalParameters)
                              return (\proc-> (n, proc idd params)),
   formalParameters = Abstract.formalParameters <$> parens (sepBy (wrap fPSection) (delimiter ";"))
                      <*> optional (delimiter ":" *> qualident),
   fPSection = Abstract.fpSection <$> (True <$ keyword "VAR" <|> pure False) 
               <*> sepBy1 ident (delimiter ",") <* delimiter ":" <*> wrap formalType,
   formalType = Abstract.arrayType [] <$ keyword "ARRAY" <* keyword "OF" <*> wrap formalType 
                <|> Abstract.typeReference <$> qualident
                <|> Abstract.procedureType <$ keyword "PROCEDURE" <*> optional (wrap formalParameters),
   procedureBody = Abstract.block <$> declarationSequence
                   <*> optional (keyword "BEGIN" *> wrap statementSequence) <* keyword "END",
   forwardDeclaration = Abstract.forwardDeclaration <$ keyword "PROCEDURE" <* delimiter "^"
                        <*> identdef <*> optional (wrap formalParameters),
   statementSequence = Abstract.statementSequence <$> sepByNonEmpty (wrapAmbiguous statement) (delimiter ";"),
   statement = assignment <|> procedureCall <|> ifStatement <|> caseStatement 
               <|> whileStatement <|> repeatStatement <|> loopStatement <|> forStatement <|> withStatement 
               <|> Abstract.exitStatement <$ keyword "EXIT" 
               <|> Abstract.returnStatement <$ keyword "RETURN" <*> optional expression
               <|> pure Abstract.emptyStatement
               <?> "statement",
   assignment  =  Abstract.assignment <$> designator <* delimiter ":=" <*> expression,
   procedureCall = Abstract.procedureCall <$> designator <*> optional actualParameters,
   ifStatement = Abstract.ifStatement <$ keyword "IF"
       <*> sepByNonEmpty (wrap $ Deep.Pair <$> expression <* keyword "THEN" <*> wrap statementSequence)
                         (keyword "ELSIF")
       <*> optional (keyword "ELSE" *> wrap statementSequence) <* keyword "END",
   caseStatement = Abstract.caseStatement <$ keyword "CASE" <*> expression
       <*  keyword "OF" <*> sepByNonEmpty (wrap case_prod) (delimiter "|")
       <*> optional (keyword "ELSE" *> wrap statementSequence) <* keyword "END",
   case_prod = Abstract.caseAlternative <$> caseLabelList <* delimiter ":" <*> wrap statementSequence
               <|> pure Abstract.emptyCase,
   caseLabelList = sepByNonEmpty (wrap caseLabels) (delimiter ","),
   caseLabels = Abstract.singleLabel <$> constExpression
                <|> Abstract.labelRange <$> constExpression <* delimiter ".." <*> constExpression,
   whileStatement = Abstract.whileStatement <$ keyword "WHILE" <*> expression <* keyword "DO"
                    <*> wrap statementSequence <* keyword "END",
   repeatStatement = Abstract.repeatStatement <$ keyword "REPEAT"
                     <*> wrap statementSequence <* keyword "UNTIL" <*> expression,
   loopStatement = Abstract.loopStatement <$ keyword "LOOP" <*> wrap statementSequence <* keyword "END",
   forStatement = empty,
   withStatement = Abstract.withStatement <$ keyword "WITH"
                   <*> wrap (Abstract.withAlternative <$> qualident <* delimiter ":" <*> qualident
                             <* keyword "DO" <*> wrap statementSequence)
                   <* keyword "END"}

wrapAmbiguous, wrap :: Abstract.Oberon l => Parser (OberonGrammar l f) Text a -> Parser (OberonGrammar l f) Text (NodeWrap a)
wrapAmbiguous = (Compose <$>) . ((,) <$> getSourcePos <*>) . ambiguous
wrap = wrapAmbiguous

wrapBinary :: (NodeWrap a -> NodeWrap a -> a) -> (NodeWrap a -> NodeWrap a -> NodeWrap a)
wrapBinary op a@(Compose (pos, a')) b = Compose (pos, pure (op a b))

moptional p = p <|> mempty

delimiter, operator :: Abstract.Oberon l => Text -> Parser (OberonGrammar l f) Text Text

delimiter s = lexicalToken (string s) <?> ("delimiter " <> show s)
operator s = lexicalToken (string s) <?> ("operator " <> show s)

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
