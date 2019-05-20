{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances,
             StandaloneDeriving, TemplateHaskell, TypeFamilies #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}

-- | Oberon Abstract Syntax Tree definitions

module Language.Oberon.AST (module Language.Oberon.AST, RelOp(..)) where

import Data.Data (Data, Typeable)
import Data.List.NonEmpty
import Data.Text (Text)

import Transformation.Deep (Product)
import qualified Transformation.Deep.TH
import qualified Rank2.TH

import qualified Language.Oberon.Abstract as Abstract
import Language.Oberon.Abstract (RelOp(..))

data Language = Language deriving (Data, Typeable)

instance Abstract.Wirthy Language where
   type Module Language = Module Language
   type Declaration Language = Declaration Language
   type Type Language = Type Language
   type Statement Language = Statement Language
   type Expression Language = Expression Language
   type Designator Language = Designator Language

   type Import Language = Import Language
   type FieldList Language = FieldList Language
   type ProcedureHeading Language = ProcedureHeading Language
   type FormalParameters Language = FormalParameters Language
   type FPSection Language = FPSection Language
   type Block Language = Block Language
   type StatementSequence Language = StatementSequence Language
   type Case Language = Case Language
   type CaseLabels Language = CaseLabels Language
   type Element Language = Element Language

   type IdentDef Language = IdentDef Language
   type QualIdent Language = QualIdent Language

   -- Declaration
   constantDeclaration = ConstantDeclaration
   typeDeclaration = TypeDeclaration
   variableDeclaration = VariableDeclaration
   procedureDeclaration = ProcedureDeclaration

   formalParameters = FormalParameters
   fpSection = FPSection
   block = Block
   
   fieldList = FieldList
   emptyFieldList = EmptyFieldList

   -- Type
   pointerType = PointerType
   procedureType = ProcedureType
   typeReference = TypeReference

   -- Statement
   assignment = Assignment
   caseStatement = CaseStatement
   emptyStatement = EmptyStatement
   exitStatement = Exit
   ifStatement = If
   loopStatement = Loop
   procedureCall = ProcedureCall
   repeatStatement = Repeat
   returnStatement = Return
   whileStatement = While

   caseAlternative = Case
   emptyCase = EmptyCase
   labelRange = LabelRange
   singleLabel = SingleLabel
   
   statementSequence = StatementSequence

   -- Expression
   add = Add
   subtract = Subtract
   and = And
   or = Or
   divide = Divide
   integerDivide = IntegerDivide
   modulo = Modulo
   multiply = Multiply
   functionCall = FunctionCall
   integer = Integer
   negative = Negative
   positive = Positive
   nil = Nil
   not = Not
   read = Read
   real = Real
   relation = Relation
   string = String
   charCode = CharCode

   element = Element
   range = Range

   -- Designator
   variable = Variable
   field = Field
   index = Index
   dereference = Dereference

   -- Identifier
   identDef = flip IdentDef PrivateOnly
   nonQualIdent = NonQualIdent

instance Abstract.CoWirthy Language where
   coDeclaration (ConstantDeclaration name value) = Just (Abstract.constantDeclaration name value)
   coDeclaration (TypeDeclaration name ty) = Just (Abstract.typeDeclaration name ty)
   coDeclaration (VariableDeclaration name ty) = Just (Abstract.variableDeclaration name ty)
--   coDeclaration (ProcedureDeclaration name ty) = Abstract.procedureDeclaration <$> Abstract.coIdentDef name <*> traverse Abstract.coType ty
   coDeclaration ForwardDeclaration{} = Nothing
   
--   coType (TypeReference q) = Just (Abstract.typeReference q)
--   coType (ProcedureType params) = Just (Abstract.procedureType params)
   coType (PointerType destination) = Just (Abstract.pointerType destination)
   coType _ = Nothing
   
   coStatement EmptyStatement = Just Abstract.emptyStatement
   coStatement (Assignment destination expression) = Just (Abstract.assignment destination expression)
   coStatement (ProcedureCall procedure parameters) = Just (Abstract.procedureCall procedure parameters)
--   coStatement (If branches fallback) = Just (Abstract.ifStatement branches fallback)
--   coStatement (CaseStatement scrutinee cases fallback) = Just (Abstract.caseStatement scrutinee cases fallback)
   coStatement (While condition body) = Just (Abstract.whileStatement condition body)
   coStatement (Repeat body condition) = Just (Abstract.repeatStatement body condition)
   coStatement (For index from to by body) = Nothing
   coStatement (Loop body) = Just (Abstract.loopStatement body)
   coStatement (With alternatives fallback) = Nothing
   coStatement Exit = Just Abstract.exitStatement
   coStatement (Return result) = Just (Abstract.returnStatement result)
   
   coExpression (Relation op left right) = Just (Abstract.relation op left right)
   coExpression (IsA left right) = Nothing
   coExpression (Positive e) = Just (Abstract.positive e)
   coExpression (Negative e) = Just (Abstract.negative e)
   coExpression (Add left right) = Just (Abstract.add left right)
   coExpression (Subtract left right) = Just (Abstract.subtract left right)
   coExpression (Or left right) = Just (Abstract.or left right)
   coExpression (Multiply left right) = Just (Abstract.multiply left right)
   coExpression (Divide left right) = Just (Abstract.divide left right)
   coExpression (IntegerDivide left right) = Just (Abstract.integerDivide left right)
   coExpression (Modulo left right) = Just (Abstract.modulo left right)
   coExpression (And left right) = Just (Abstract.and left right)
   coExpression (Integer n) = Just (Abstract.integer n)
   coExpression (Real r) = Just (Abstract.real r)
   coExpression (String s) = Just (Abstract.string s)
   coExpression (CharCode c) = Just (Abstract.charCode c)
   coExpression Nil = Just Abstract.nil
   coExpression (Set elements) = Nothing
   coExpression (Read var) = Just (Abstract.read var)
   coExpression (FunctionCall function parameters) = Just (Abstract.functionCall function parameters)
   coExpression (Not e) = Just (Abstract.not e)
   
--   coDesignator (Variable q) = Just (Abstract.variable q)
   coDesignator (Field record name) = Just (Abstract.field record name)
   coDesignator (Index array indexes) = Just (Abstract.index array indexes)
   coDesignator (TypeGuard scrutinee typeName) = Nothing
   coDesignator (Dereference pointer) = Just (Abstract.dereference pointer)

instance Abstract.Nameable Language where
   getProcedureName (ProcedureHeading _ iddef _) = Abstract.getIdentDefName iddef
   getProcedureName (TypeBoundHeading _ _ _ _ iddef _) = Abstract.getIdentDefName iddef
   getIdentDefName (IdentDef name _) = name
   getNonQualIdentName (NonQualIdent name) = Just name
   getNonQualIdentName _ = Nothing

instance Abstract.Oberon Language where
   type WithAlternative Language = WithAlternative Language
   moduleUnit = Module
   moduleImport = (,)
   exported = flip IdentDef Exported
   qualIdent = QualIdent
   getQualIdentNames (QualIdent moduleName name) = Just (moduleName, name)
   getQualIdentNames _ = Nothing

   arrayType = ArrayType
   recordType = RecordType
   procedureHeading = ProcedureHeading
   forwardDeclaration = ForwardDeclaration
   withStatement alt = With (alt :| []) Nothing
   withAlternative = WithAlternative
   is = IsA
   set = Set
   typeGuard = TypeGuard

instance Abstract.Oberon2 Language where
   readOnly = flip IdentDef ReadOnly
   typeBoundHeading = TypeBoundHeading
   forStatement = For
   variantWithStatement = With

data Module λ l f' f =
   Module Ident [Import l] [f (Abstract.Declaration l l f' f')] (Maybe (f (Abstract.StatementSequence l l f' f')))

deriving instance (Typeable λ, Typeable l, Typeable f, Typeable f', Data (Abstract.Import l),
                   Data (f (Abstract.Declaration l l f' f')), Data (f (Abstract.StatementSequence l l f' f'))) =>
                  Data (Module λ l f' f)
deriving instance (Show (Abstract.Import l), Show (f (Abstract.Declaration l l f' f')),
                   Show (f (Abstract.StatementSequence l l f' f'))) =>
                  Show (Module λ l f' f)

type Ident = Text

type Import l = (Maybe Ident, Ident)

data Declaration λ l f' f = ConstantDeclaration (Abstract.IdentDef l) (f (Abstract.ConstExpression l l f' f'))
                          | TypeDeclaration (Abstract.IdentDef l) (f (Abstract.Type l l f' f'))
                          | VariableDeclaration (Abstract.IdentList l) (f (Abstract.Type l l f' f'))
                          | ProcedureDeclaration (f (Abstract.ProcedureHeading l l f' f'))
                                                 (f (Abstract.Block l l f' f'))
                          | ForwardDeclaration (Abstract.IdentDef l) (Maybe (f (Abstract.FormalParameters l l f' f')))

deriving instance (Typeable λ, Typeable l, Typeable f, Typeable f',
                   Data (f (Abstract.Type l l f' f')), Data (f (Abstract.ConstExpression l l f' f')),
                   Data (f (Abstract.FormalParameters l l f' f')), Data (f (Abstract.ProcedureHeading l l f' f')),
                   Data (f (Abstract.Block l l f' f')), Data (Abstract.IdentDef l)) => Data (Declaration λ l f' f)
deriving instance (Show (f (Abstract.Type l l f' f')), Show (f (Abstract.ConstExpression l l f' f')),
                   Show (f (Abstract.FormalParameters l l f' f')), Show (f (Abstract.ProcedureHeading l l f' f')),
                   Show (f (Abstract.Block l l f' f')), Show (Abstract.IdentDef l)) => Show (Declaration λ l f' f)

data QualIdent l = QualIdent Ident Ident 
                 | NonQualIdent Ident
   deriving (Data, Eq, Ord, Show)

data IdentDef l = IdentDef Ident AccessMode
   deriving (Data, Eq, Ord, Show)

data AccessMode = Exported | ReadOnly | PrivateOnly
   deriving (Data, Eq, Ord, Show)

data Expression λ l f' f = Relation RelOp (f (Abstract.Expression l l f' f')) (f (Abstract.Expression l l f' f'))
                         | IsA (f (Abstract.Expression l l f' f')) (Abstract.QualIdent l)
                         | Positive (f (Abstract.Expression l l f' f'))
                         | Negative (f (Abstract.Expression l l f' f'))
                         | Add (f (Abstract.Expression l l f' f')) (f (Abstract.Expression l l f' f'))
                         | Subtract (f (Abstract.Expression l l f' f')) (f (Abstract.Expression l l f' f'))
                         | Or (f (Abstract.Expression l l f' f')) (f (Abstract.Expression l l f' f'))
                         | Multiply (f (Abstract.Expression l l f' f')) (f (Abstract.Expression l l f' f'))
                         | Divide (f (Abstract.Expression l l f' f')) (f (Abstract.Expression l l f' f'))
                         | IntegerDivide (f (Abstract.Expression l l f' f')) (f (Abstract.Expression l l f' f'))
                         | Modulo (f (Abstract.Expression l l f' f')) (f (Abstract.Expression l l f' f'))
                         | And (f (Abstract.Expression l l f' f')) (f (Abstract.Expression l l f' f'))
                         | Integer Text
                         | Real Text
                         | CharCode Int
                         | String Text
                         | Nil 
                         | Set [f (Abstract.Element l l f' f')]
                         | Read (f (Abstract.Designator l l f' f'))
                         | FunctionCall (f (Abstract.Designator l l f' f')) [f (Abstract.Expression l l f' f')]
                         | Not (f (Abstract.Expression l l f' f'))

deriving instance (Typeable λ, Typeable l, Typeable f, Typeable f', Data (Abstract.QualIdent l),
                   Data (f (Abstract.Designator l l f' f')), Data (f (Abstract.Element l l f' f')),
                   Data (f (Abstract.Expression l l f' f'))) =>
                  Data (Expression λ l f' f)
deriving instance (Show (Abstract.QualIdent l), Show (f (Abstract.Designator l l f' f')),
                   Show (f (Abstract.Element l l f' f')), Show (f (Abstract.Expression l l f' f'))) =>
                  Show (Expression λ l f' f)
deriving instance (Eq (Abstract.QualIdent l), Eq (f (Abstract.Designator l l f' f')), Eq (f (Abstract.Element l l f' f')),
                  Eq (f (Abstract.Expression l l f' f'))) => Eq (Expression λ l f' f)

data Element λ l f' f = Element (f (Abstract.Expression l l f' f'))
                      | Range (f (Abstract.Expression l l f' f')) (f (Abstract.Expression l l f' f'))

deriving instance (Typeable λ, Typeable l, Typeable f, Typeable f', Data (f (Abstract.Expression l l f' f'))) => Data (Element λ l f' f)
deriving instance Show (f (Abstract.Expression l l f' f')) => Show (Element λ l f' f)
deriving instance Eq (f (Abstract.Expression l l f' f')) => Eq (Element λ l f' f)

data Designator λ l f' f = Variable (Abstract.QualIdent l)
                         | Field (f (Abstract.Designator l l f' f')) Ident 
                         | Index (f (Abstract.Designator l l f' f')) (NonEmpty (f (Abstract.Expression l l f' f')))
                         | TypeGuard (f (Abstract.Designator l l f' f')) (Abstract.QualIdent l)
                         | Dereference (f (Abstract.Designator l l f' f'))

deriving instance (Typeable λ, Typeable l, Typeable f, Typeable f', Data (Abstract.QualIdent l),
                   Data (f (Abstract.Designator l l f' f')), Data (f (Abstract.Expression l l f' f'))) =>
                  Data (Designator λ l f' f)
deriving instance (Show (Abstract.QualIdent l), Show (f (Abstract.Designator l l f' f')),
                   Show (f (Abstract.Expression l l f' f'))) => Show (Designator λ l f' f)
deriving instance (Eq (Abstract.QualIdent l), Eq (f (Abstract.Designator l l f' f')),
                   Eq (f (Abstract.Expression l l f' f'))) => Eq (Designator λ l f' f)

data Type λ l f' f = TypeReference (Abstract.QualIdent l)
                   | ArrayType [f (Abstract.ConstExpression l l f' f')] (f (Abstract.Type l l f' f'))
                   | RecordType (Maybe (Abstract.BaseType l)) (NonEmpty (f (Abstract.FieldList l l f' f')))
                   | PointerType (f (Abstract.Type l l f' f'))
                   | ProcedureType (Maybe (f (Abstract.FormalParameters l l f' f')))

deriving instance (Typeable λ, Typeable l, Typeable f, Typeable f', Data (Abstract.QualIdent l), Data (f (Abstract.Type l l f' f')),
                   Data (f (Abstract.ConstExpression l l f' f')), Data (f (Abstract.FormalParameters l l f' f')),
                   Data (f (Abstract.FieldList l l f' f'))) =>
                  Data (Type λ l f' f)
deriving instance (Show (Abstract.QualIdent l), Show (f (Abstract.Type l l f' f')),
                   Show (f (Abstract.ConstExpression l l f' f')), Show (f (Abstract.FormalParameters l l f' f')),
                   Show (f (Abstract.FieldList l l f' f'))) =>
                  Show (Type λ l f' f)

data FieldList λ l f' f = FieldList (Abstract.IdentList l) (f (Abstract.Type l l f' f'))
                        | EmptyFieldList

deriving instance (Typeable λ, Typeable l, Typeable f, Typeable f', Data (Abstract.IdentDef l), Data (f (Abstract.Type l l f' f')),
                   Data (f (Abstract.Expression l l f' f'))) => Data (FieldList λ l f' f)
deriving instance (Show (Abstract.IdentDef l), Show (f (Abstract.Type l l f' f')), Show (f (Abstract.Expression l l f' f'))) =>
                  Show (FieldList λ l f' f)

data ProcedureHeading λ l f' f =
   ProcedureHeading                    Bool (Abstract.IdentDef l) (Maybe (f (Abstract.FormalParameters l l f' f')))
   | TypeBoundHeading Bool Ident Ident Bool (Abstract.IdentDef l) (Maybe (f (Abstract.FormalParameters l l f' f')))

data FormalParameters λ l f' f = FormalParameters [f (Abstract.FPSection l l f' f')] (Maybe (Abstract.ReturnType l))

data FPSection λ l f' f = FPSection Bool [Ident] (f (Abstract.Type l l f' f'))

deriving instance (Typeable λ, Typeable l, Typeable f, Typeable f', Data (Abstract.IdentDef l),
                   Data (f (Abstract.FormalParameters l l f' f'))) => Data (ProcedureHeading λ l f' f)
deriving instance (Show (Abstract.IdentDef l), Show (f (Abstract.FormalParameters l l f' f'))) =>
                  Show (ProcedureHeading λ l f' f)

deriving instance (Typeable λ, Typeable l, Typeable f, Typeable f', Data (Abstract.ReturnType l),
                   Data (f (Abstract.FPSection l l f' f')),  Data (f (Abstract.Expression l l f' f'))) =>
                  Data (FormalParameters λ l f' f)
deriving instance (Show (f (Abstract.FPSection l l f' f')), Show (Abstract.ReturnType l),
                   Show (f (Abstract.Expression l l f' f'))) => Show (FormalParameters λ l f' f)

deriving instance (Typeable λ, Typeable l, Typeable f, Typeable f', Data (f (Abstract.Type l l f' f')),
                   Data (f (Abstract.Expression l l f' f'))) => Data (FPSection λ l f' f)
deriving instance (Show (f (Abstract.Type l l f' f')), Show (f (Abstract.Expression l l f' f'))) => Show (FPSection λ l f' f)

data Block λ l f' f = Block [f (Abstract.Declaration l l f' f')] (Maybe (f (Abstract.StatementSequence l l f' f')))

deriving instance (Typeable λ, Typeable l, Typeable f, Typeable f', Data (f (Abstract.Declaration l l f' f')),
                   Data (f (Abstract.Designator l l f' f')), Data (f (Abstract.Expression l l f' f')),
                   Data (f (Abstract.StatementSequence l l f' f'))) =>
                  Data (Block λ l f' f)
deriving instance (Show (f (Abstract.Declaration l l f' f')), Show (f (Abstract.Designator l l f' f')),
                   Show (f (Abstract.Expression l l f' f')), Show (f (Abstract.StatementSequence l l f' f'))) =>
                  Show (Block λ l f' f)

newtype StatementSequence λ l f' f = StatementSequence (NonEmpty (f (Abstract.Statement l l f' f')))

deriving instance (Typeable λ, Typeable l, Typeable f, Typeable f', Data (f (Abstract.Statement l l f' f'))) =>
                  Data (StatementSequence λ l f' f)
deriving instance Show (f (Abstract.Statement l l f' f')) => Show (StatementSequence λ l f' f)

data Statement λ l f' f = EmptyStatement
                        | Assignment (f (Abstract.Designator l l f' f')) (f (Abstract.Expression l l f' f'))
                        | ProcedureCall (f (Abstract.Designator l l f' f')) (Maybe [f (Abstract.Expression l l f' f')])
                        | If (NonEmpty (f (Product (Abstract.Expression l l) (Abstract.StatementSequence l l) f' f')))
                             (Maybe (f (Abstract.StatementSequence l l f' f')))
                        | CaseStatement (f (Abstract.Expression l l f' f')) 
                                        (NonEmpty (f (Abstract.Case l l f' f'))) 
                                        (Maybe (f (Abstract.StatementSequence l l f' f')))
                        | While (f (Abstract.Expression l l f' f')) (f (Abstract.StatementSequence l l f' f'))
                        | Repeat (f (Abstract.StatementSequence l l f' f')) (f (Abstract.Expression l l f' f'))
                        | For Ident (f (Abstract.Expression l l f' f')) (f (Abstract.Expression l l f' f')) 
                              (Maybe (f (Abstract.Expression l l f' f'))) (f (Abstract.StatementSequence l l f' f'))  -- Oberon2
                        | Loop (f (Abstract.StatementSequence l l f' f'))
                        | With (NonEmpty (f (Abstract.WithAlternative l l f' f')))
                               (Maybe (f (Abstract.StatementSequence l l f' f')))
                        | Exit
                        | Return (Maybe (f (Abstract.Expression l l f' f')))

deriving instance (Typeable λ, Typeable l, Typeable f, Typeable f',
                   Data (f (Abstract.Designator l l f' f')), Data (f (Abstract.Expression l l f' f')),
                   Data (f (Product (Abstract.Expression l l) (Abstract.StatementSequence l l) f' f')),
                   Data (f (Abstract.Case l l f' f')), Data (f (Abstract.WithAlternative l l f' f')),
                   Data (f (Abstract.StatementSequence l l f' f'))) => Data (Statement λ l f' f)
deriving instance (Show (f (Abstract.Designator l l f' f')), Show (f (Abstract.Expression l l f' f')),
                   Show (f (Product (Abstract.Expression l l) (Abstract.StatementSequence l l) f' f')),
                   Show (f (Abstract.Case l l f' f')), Show (f (Abstract.WithAlternative l l f' f')),
                   Show (f (Abstract.StatementSequence l l f' f'))) => Show (Statement λ l f' f)

data WithAlternative λ l f' f = WithAlternative (Abstract.QualIdent l) (Abstract.QualIdent l)
                                                (f (Abstract.StatementSequence l l f' f'))

data Case λ l f' f = Case (NonEmpty (f (Abstract.CaseLabels l l f' f'))) (f (Abstract.StatementSequence l l f' f'))
                   | EmptyCase

data CaseLabels λ l f' f = SingleLabel (f (Abstract.ConstExpression l l f' f'))
                         | LabelRange (f (Abstract.ConstExpression l l f' f')) (f (Abstract.ConstExpression l l f' f'))

deriving instance (Typeable λ, Typeable l, Typeable f, Typeable f', Data (Abstract.QualIdent l),
                   Data (f (Abstract.Designator l l f' f')), Data (f (Abstract.StatementSequence l l f' f'))) =>
                  Data (WithAlternative λ l f' f)
deriving instance (Show (Abstract.QualIdent l), Show (f (Abstract.StatementSequence l l f' f'))) =>
                  Show (WithAlternative λ l f' f)

deriving instance (Typeable λ, Typeable l, Typeable f, Typeable f', Show (Abstract.QualIdent l),
                   Data (f (Abstract.CaseLabels l l f' f')), Data (f (Abstract.StatementSequence l l f' f'))) =>
                  Data (Case λ l f' f)
deriving instance (Show (f (Abstract.CaseLabels l l f' f')), Show (f (Abstract.StatementSequence l l f' f'))) =>
                  Show (Case λ l f' f)

deriving instance (Typeable λ, Typeable l, Typeable f, Typeable f', Data (f (Abstract.ConstExpression l l f' f'))) =>
                  Data (CaseLabels λ l f' f)
deriving instance Show (f (Abstract.ConstExpression l l f' f')) => Show (CaseLabels λ l f' f)

$(mconcat <$> mapM Transformation.Deep.TH.deriveAll
  [''Module, ''Declaration, ''Type, ''Expression,
   ''Element, ''Designator, ''FieldList,
   ''ProcedureHeading, ''FormalParameters, ''FPSection, ''Block,
   ''Statement, ''StatementSequence, ''WithAlternative, ''Case, ''CaseLabels])
