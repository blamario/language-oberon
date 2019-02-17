{-# Language OverloadedStrings, Rank2Types, RecordWildCards, TypeFamilies, TemplateHaskell #-}

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
import Numeric (readHex)
import Data.Text (Text, unpack)
import Text.Grampa
import Text.Grampa.ContextFree.LeftRecursive (Parser)
import Text.Parser.Combinators (sepBy, sepBy1, sepByNonEmpty, try)
import Text.Parser.Token (braces, brackets, parens)

import Transformation.Deep as Deep (Product(Pair))
import qualified Rank2
import qualified Rank2.TH

import Language.Oberon.AST

import Prelude hiding (length, takeWhile)

-- | All the productions of the Oberon grammar
data OberonGrammar f p = OberonGrammar {
   module_prod :: p (Module f f),
   ident :: p Ident,
   letter :: p Text,
   digit :: p Text,
   importList :: p [Import],
   import_prod :: p Import,
   declarationSequence :: p [f (Declaration f f)],
   constantDeclaration :: p (Declaration f f),
   identdef :: p IdentDef,
   constExpression :: p (f (Expression f f)),
   expression :: p (f (Expression f f)),
   simpleExpression :: p (f (Expression f f)),
   term :: p (f (Expression f f)),
   factor :: p (f (Expression f f)),
   number :: p (Expression f f),
   integer :: p (Expression f f),
   hexDigit :: p Text,
   real :: p (Expression f f),
   scaleFactor :: p Text,
   charConstant :: p (Expression f f),
   string_prod :: p Text,
   set :: p (Expression f f),
   element :: p (Element f f),
   designator :: p (f (Designator f f)),
   expList :: p (NonEmpty (f (Expression f f))),
   actualParameters :: p [f (Expression f f)],
   mulOperator :: p (BinOp f),
   addOperator :: p (BinOp f),
   relation :: p RelOp,
   typeDeclaration :: p (Declaration f f),
   type_prod :: p (Type f f),
   qualident :: p QualIdent,
   arrayType :: p (Type f f),
   length :: p (f (Expression f f)),
   recordType :: p (Type f f),
   baseType :: p QualIdent,
   fieldListSequence :: p (NonEmpty (f (FieldList f f))),
   fieldList :: p (FieldList f f),
   identList :: p IdentList,
   pointerType :: p (Type f f),
   procedureType :: p (Type f f),
   variableDeclaration :: p (Declaration f f),
   procedureDeclaration :: p (Declaration f f),
   procedureHeading :: p (ProcedureHeading f f),
   formalParameters :: p (FormalParameters f f),
   fPSection :: p (FPSection f f),
   formalType :: p (Type f f),
   procedureBody :: p (ProcedureBody f f),
   forwardDeclaration :: p (Declaration f f),
   statementSequence :: p (StatementSequence f f),
   statement :: p (Statement f f),
   assignment :: p (Statement f f),
   procedureCall :: p (Statement f f),
   ifStatement :: p (Statement f f),
   caseStatement :: p (Statement f f),
   case_prod :: p (Case f f),
   caseLabelList :: p (NonEmpty (f (CaseLabels f f))),
   caseLabels :: p (CaseLabels f f),
   whileStatement :: p (Statement f f),
   repeatStatement :: p (Statement f f),
   forStatement :: p (Statement f f),
   loopStatement :: p (Statement f f),
   withStatement :: p (Statement f f)}

newtype BinOp f = BinOp {applyBinOp :: (f (Expression f f) -> f (Expression f f) -> f (Expression f f))}

instance Show (BinOp f) where
   show = const "BinOp{}"

$(Rank2.TH.deriveAll ''OberonGrammar)

instance Lexical (OberonGrammar f) where
   type LexicalConstraint p (OberonGrammar f) s = (s ~ Text, p ~ Parser)
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
   :: Grammar (OberonGrammar NodeWrap) Parser Text
-- | Grammar of an Oberon module
oberonGrammar = fixGrammar grammar
-- | Grammar of an Oberon-2 module
oberon2Grammar = fixGrammar grammar2
-- | Grammar of an Oberon definition module
oberonDefinitionGrammar = fixGrammar definitionGrammar
-- | Grammar of an Oberon-2 definition module
oberon2DefinitionGrammar = fixGrammar definitionGrammar2

grammar, definitionGrammar :: GrammarBuilder (OberonGrammar NodeWrap) (OberonGrammar NodeWrap) Parser Text

definitionGrammar g@OberonGrammar{..} = definitionMixin (grammar g)

definitionGrammar2 g@OberonGrammar{..} = definitionMixin (grammar2 g)

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
                    return (Module name imports declarations Nothing),
   procedureDeclaration = ProcedureDeclaration <$> procedureHeading <*> (pure $ ProcedureBody [] Nothing),
   identdef = IdentDef <$> ident <*> pure Exported <* optional (delimiter "*")}

grammar2 g@OberonGrammar{..} = g1{
   identdef = IdentDef <$> ident <*> (Exported <$ delimiter "*" <|> ReadOnly <$ delimiter "-" <|> pure PrivateOnly),
   
   string_prod = string_prod1 <|> lexicalToken (char '\'' *> takeWhile (/= "'") <* char '\''),
   procedureHeading = ProcedureHeading <$ keyword "PROCEDURE"
                      <*> optional (parens
                                    ((,,) <$> (True <$ keyword "VAR" <|> pure False)
                                          <*> ident <* delimiter ":" <*> ident))
                      <*> (True <$ delimiter "*" <|> pure False) 
                      <*> identdef <*> optional (wrap formalParameters),
   arrayType = 
      ArrayType <$ keyword "ARRAY" <*> sepBy length (delimiter ",") <* keyword "OF" <*> wrap type_prod,
   statement = statement1 <|> forStatement,
   forStatement = 
      For <$ keyword "FOR" <*> ident <* delimiter ":=" <*> expression <* keyword "TO" <*> expression
      <*> optional (keyword "BY" *> constExpression) <* keyword "DO"
      <*> wrap statementSequence <* keyword "END",
   withStatement = With <$ keyword "WITH" <*> sepByNonEmpty (wrap withAlternative) (delimiter "|")
                        <*> optional (keyword "ELSE" *> wrap statementSequence) <* keyword "END"}
   where g1@OberonGrammar{statement= statement1, string_prod= string_prod1} = grammar g
         withAlternative = WithAlternative <$> qualident <* delimiter ":" <*> qualident
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
                    return (Module name imports declarations body),
   ident = identifier,
   letter = satisfyCharInput isLetter,
   digit = satisfyCharInput isDigit,
   importList = keyword "IMPORT" *> sepBy1 import_prod (delimiter ",") <* delimiter ";",
   import_prod = (,) <$> optional (ident <* delimiter ":=") <*> ident,
   declarationSequence = concatMany (keyword "CONST" *> many (wrap constantDeclaration <* delimiter ";")
                                     <|> keyword "TYPE" *> many (wrap typeDeclaration <* delimiter ";")
                                     <|> keyword "VAR" *> many (wrap variableDeclaration <* delimiter ";"))
                         <> many (wrap procedureDeclaration <* delimiter ";"
                                  <|> wrap forwardDeclaration <* delimiter ";")
                         <?> "declarations",
   constantDeclaration = ConstantDeclaration <$> identdef <* delimiter "=" <*> constExpression,
   identdef = IdentDef <$> ident <*> (Exported <$ delimiter "*" <|> pure PrivateOnly),
   constExpression = expression,
   expression = simpleExpression
                <|> wrap (flip Relation <$> simpleExpression <*> relation <*> simpleExpression)
                <?> "expression",
   simpleExpression = 
      (wrap (Positive <$ operator "+" <*> term) <|> wrap (Negative <$ operator "-" <*> term) <|> term)
      <**> (appEndo <$> concatMany (Endo <$> (flip . applyBinOp <$> addOperator <*> term))),
   term = factor <**> (appEndo <$> concatMany (Endo <$> (flip . applyBinOp <$> mulOperator <*> factor))),
   factor = wrapAmbiguous (number
                           <|> charConstant
                           <|> String <$> string_prod
                           <|> Nil <$ keyword "NIL"
                           <|> set
                           <|> Read <$> designator
                           <|> FunctionCall <$> designator <*> actualParameters
                           <|> Not <$ operator "~" <*> factor)
            <|> parens expression,
   number  =  integer <|> real,
   integer = Integer <$> lexicalToken (digit <> (takeCharsWhile isDigit <|> takeCharsWhile isHexDigit <> string "H")),
   hexDigit = satisfyCharInput isHexDigit,
   real = Real <$> lexicalToken (digit <> takeCharsWhile isDigit <> string "."
                                 *> takeCharsWhile isDigit <> moptional scaleFactor),
   scaleFactor = (string "E" <|> string "D") <> moptional (string "+" <|> string "-") <> digit <> takeCharsWhile isDigit,
   charConstant = lexicalToken (empty -- CharConstant <$ char '"' <*> anyChar <* char '"'
                                <|> CharCode . fst . head . readHex . unpack
                                <$> (digit <> takeCharsWhile isHexDigit <* string "X")),
   string_prod = lexicalToken (char '"' *> takeWhile (/= "\"") <* char '"'),
   set = Set <$> braces (sepBy (wrap element) (delimiter ",")),
   element = Element <$> expression
             <|> Range <$> expression <* delimiter ".." <*> expression,
   designator = wrapAmbiguous $
                    Variable <$> qualident
                <|> Field <$> designator <* delimiter "." <*> ident
                <|> Index <$> designator <*> brackets expList
                <|> TypeGuard <$> designator <*> parens qualident
                <|> Dereference <$> designator <* operator "^",
   expList = sepByNonEmpty expression (delimiter ","),
   actualParameters = parens (sepBy expression (delimiter ",")),
   mulOperator = BinOp . wrapBinary
                 <$> (Multiply <$ operator "*" <|> Divide <$ operator "/"
                      <|> IntegerDivide <$ keyword "DIV" <|> Modulo <$ keyword "MOD" <|> And <$ operator "&"),
   addOperator = BinOp . wrapBinary <$> (Add <$ operator "+" <|> Subtract <$ operator "-" <|> Or <$ keyword "OR"),
   relation = Equal <$ operator "=" <|> Unequal <$ operator "#" 
              <|> Less <$ operator "<" <|> LessOrEqual <$ operator "<=" 
              <|> Greater <$ operator ">" <|> GreaterOrEqual <$ operator ">=" 
              <|> In <$ keyword "IN" <|> Is <$ keyword "IS",
   typeDeclaration = TypeDeclaration <$> identdef <* delimiter "=" <*> wrap type_prod,
   type_prod = TypeReference <$> qualident 
               <|> arrayType 
               <|> recordType 
               <|> pointerType 
               <|> procedureType,
   qualident = QualIdent <$> ident <* delimiter "." <*> ident
               <|> NonQualIdent <$> ident,
   arrayType = ArrayType <$ keyword "ARRAY" <*> sepBy1 length (delimiter ",") <* keyword "OF" <*> wrap type_prod,
   length = constExpression,
   recordType = RecordType <$ keyword "RECORD" <*> optional (parens baseType)
                <*> fieldListSequence <* keyword "END",
   baseType = qualident,
   fieldListSequence = sepByNonEmpty (wrap fieldList) (delimiter ";"),
   fieldList = (FieldList <$> identList <* delimiter ":" <*> wrap type_prod <?> "record field declarations")
               <|> pure EmptyFieldList,
   identList = sepByNonEmpty identdef (delimiter ","),
   pointerType = PointerType <$ keyword "POINTER" <* keyword "TO" <*> wrap type_prod,
   procedureType = ProcedureType <$ keyword "PROCEDURE" <*> optional (wrap formalParameters),
   variableDeclaration = VariableDeclaration <$> identList <* delimiter ":" <*> wrap type_prod,
   procedureDeclaration = do heading <- procedureHeading
                             delimiter ";"
                             body <- procedureBody
                             let ProcedureHeading _  _ (IdentDef procedureName _) _ = heading
                             lexicalToken (string procedureName)
                             return (ProcedureDeclaration heading body),
   procedureHeading = ProcedureHeading Nothing <$ keyword "PROCEDURE" <*> (True <$ delimiter "*" <|> pure False) 
                      <*> identdef <*> optional (wrap formalParameters),
   formalParameters = FormalParameters <$> parens (sepBy (wrap fPSection) (delimiter ";"))
                      <*> optional (delimiter ":" *> qualident),
   fPSection = FPSection <$> (True <$ keyword "VAR" <|> pure False) 
               <*> sepByNonEmpty ident (delimiter ",") <* delimiter ":" <*> wrap formalType,
   formalType = ArrayType [] <$ keyword "ARRAY" <* keyword "OF" <*> wrap formalType 
                <|> TypeReference <$> qualident
                <|> ProcedureType <$ keyword "PROCEDURE" <*> optional (wrap formalParameters),
   procedureBody = ProcedureBody <$> declarationSequence
                   <*> optional (keyword "BEGIN" *> wrap statementSequence) <* keyword "END",
   forwardDeclaration = ForwardDeclaration <$ keyword "PROCEDURE" <* delimiter "^"
                        <*> identdef <*> optional (wrap formalParameters),
   statementSequence = StatementSequence <$> sepByNonEmpty (wrapAmbiguous statement) (delimiter ";"),
   statement = assignment <|> procedureCall <|> ifStatement <|> caseStatement 
               <|> whileStatement <|> repeatStatement <|> loopStatement <|> withStatement 
               <|> Exit <$ keyword "EXIT" 
               <|> Return <$ keyword "RETURN" <*> optional expression
               <|> pure EmptyStatement
               <?> "statement",
   assignment  =  Assignment <$> designator <* delimiter ":=" <*> expression,
   procedureCall = ProcedureCall <$> designator <*> optional actualParameters,
   ifStatement = If <$ keyword "IF"
       <*> sepByNonEmpty (wrap $ Deep.Pair <$> expression <* keyword "THEN" <*> wrap statementSequence)
                         (keyword "ELSIF")
       <*> optional (keyword "ELSE" *> wrap statementSequence) <* keyword "END",
   caseStatement = CaseStatement <$ keyword "CASE" <*> expression
       <*  keyword "OF" <*> sepByNonEmpty (wrap case_prod) (delimiter "|")
       <*> optional (keyword "ELSE" *> wrap statementSequence) <* keyword "END",
   case_prod  =  Case <$> caseLabelList <* delimiter ":" <*> wrap statementSequence
                 <|> pure EmptyCase,
   caseLabelList  =  sepByNonEmpty (wrap caseLabels) (delimiter ","),
   caseLabels = SingleLabel <$> constExpression
                <|> LabelRange <$> constExpression <* delimiter ".." <*> constExpression,
   whileStatement = While <$ keyword "WHILE" <*> expression <* keyword "DO"
                    <*> wrap statementSequence <* keyword "END",
   repeatStatement = Repeat <$ keyword "REPEAT" <*> wrap statementSequence <* keyword "UNTIL" <*> expression,
   loopStatement = Loop <$ keyword "LOOP" <*> wrap statementSequence <* keyword "END",
   forStatement = empty,
   withStatement = With <$ keyword "WITH"
                        <*> ((:| [])
                             <$> wrap (WithAlternative <$> qualident <* delimiter ":" <*> qualident
                                       <* keyword "DO" <*> wrap statementSequence))
                        <*> pure Nothing <* keyword "END"}

wrapAmbiguous, wrap :: Parser (OberonGrammar f) Text a -> Parser (OberonGrammar f) Text (NodeWrap a)
wrapAmbiguous = (Compose <$>) . ((,) <$> getSourcePos <*>) . ambiguous
wrap = wrapAmbiguous

wrapBinary :: (NodeWrap a -> NodeWrap a -> a) -> (NodeWrap a -> NodeWrap a -> NodeWrap a)
wrapBinary op a@(Compose (pos, a')) b = Compose (pos, pure (op a b))

moptional p = p <|> mempty

delimiter, operator :: Text -> Parser (OberonGrammar f) Text Text

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
