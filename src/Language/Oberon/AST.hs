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
   charCode = CharCode
   charConstant = CharConstant
   is = IsA
   set = Set
   typeGuard = TypeGuard

instance Abstract.Oberon2 Language where
   readOnly = flip IdentDef ReadOnly
   typeBoundHeading = TypeBoundHeading
   forStatement = For
   variantWithStatement = With

data Module l f' f =
   Module Ident [Import l] [f (Abstract.Declaration l f' f')] (Maybe (f (Abstract.StatementSequence l f' f')))

deriving instance (Typeable l, Typeable f, Typeable f',
                   Data (f (Abstract.Declaration l f' f')), Data (f (Abstract.StatementSequence l f' f'))) =>
                  Data (Module l f' f)
deriving instance (Show (f (Abstract.Declaration l f' f')), Show (f (Abstract.StatementSequence l f' f'))) =>
                  Show (Module l f' f)

type Ident = Text

type Import l = (Maybe Ident, Ident)

data Declaration l f' f = ConstantDeclaration (Abstract.IdentDef l) (f (Abstract.ConstExpression l f' f'))
                        | TypeDeclaration (Abstract.IdentDef l) (f (Abstract.Type l f' f'))
                        | VariableDeclaration (Abstract.IdentList l) (f (Abstract.Type l f' f'))
                        | ProcedureDeclaration (f (Abstract.ProcedureHeading l f' f'))
                                               (f (Abstract.Block l f' f'))
                        | ForwardDeclaration (Abstract.IdentDef l) (Maybe (f (Abstract.FormalParameters l f' f')))

deriving instance (Data l, Typeable f, Typeable f',
                   Data (f (Abstract.Type l f' f')), Data (f (Abstract.ConstExpression l f' f')),
                   Data (f (Abstract.FormalParameters l f' f')), Data (f (Abstract.ProcedureHeading l f' f')),
                   Data (f (Abstract.Block l f' f')), Data (Abstract.IdentDef l)) => Data (Declaration l f' f)
deriving instance (Show (f (Abstract.Type l f' f')), Show (f (Abstract.ConstExpression l f' f')),
                   Show (f (Abstract.FormalParameters l f' f')), Show (f (Abstract.ProcedureHeading l f' f')),
                   Show (f (Abstract.Block l f' f')), Show (Abstract.IdentDef l)) => Show (Declaration l f' f)

data QualIdent l = QualIdent Ident Ident 
                 | NonQualIdent Ident
   deriving (Data, Eq, Ord, Show)

data IdentDef l = IdentDef Ident AccessMode
   deriving (Data, Eq, Ord, Show)

data AccessMode = Exported | ReadOnly | PrivateOnly
   deriving (Data, Eq, Ord, Show)

data Expression l f' f = Relation RelOp (f (Abstract.Expression l f' f')) (f (Abstract.Expression l f' f'))
                       | IsA (f (Abstract.Expression l f' f')) (Abstract.QualIdent l)
                       | Positive (f (Abstract.Expression l f' f'))
                       | Negative (f (Abstract.Expression l f' f'))
                       | Add (f (Abstract.Expression l f' f')) (f (Abstract.Expression l f' f'))
                       | Subtract (f (Abstract.Expression l f' f')) (f (Abstract.Expression l f' f'))
                       | Or (f (Abstract.Expression l f' f')) (f (Abstract.Expression l f' f'))
                       | Multiply (f (Abstract.Expression l f' f')) (f (Abstract.Expression l f' f'))
                       | Divide (f (Abstract.Expression l f' f')) (f (Abstract.Expression l f' f'))
                       | IntegerDivide (f (Abstract.Expression l f' f')) (f (Abstract.Expression l f' f'))
                       | Modulo (f (Abstract.Expression l f' f')) (f (Abstract.Expression l f' f'))
                       | And (f (Abstract.Expression l f' f')) (f (Abstract.Expression l f' f'))
                       | Integer Text
                       | Real Text
                       | CharConstant Char
                       | CharCode Int
                       | String Text
                       | Nil 
                       | Set [f (Abstract.Element l f' f')]
                       | Read (f (Abstract.Designator l f' f'))
                       | FunctionCall (f (Abstract.Designator l f' f')) [f (Abstract.Expression l f' f')]
                       | Not (f (Abstract.Expression l f' f'))

deriving instance (Data l, Typeable f, Typeable f', Data (Abstract.QualIdent l),
                   Data (f (Abstract.Designator l f' f')), Data (f (Abstract.Element l f' f')),
                   Data (f (Abstract.Expression l f' f'))) =>
                  Data (Expression l f' f)
deriving instance (Show (Abstract.QualIdent l), Show (f (Abstract.Designator l f' f')),
                   Show (f (Abstract.Element l f' f')), Show (f (Abstract.Expression l f' f'))) =>
                  Show (Expression l f' f)
deriving instance (Eq (Abstract.QualIdent l), Eq (f (Abstract.Designator l f' f')), Eq (f (Abstract.Element l f' f')),
                  Eq (f (Abstract.Expression l f' f'))) => Eq (Expression l f' f)

data Element l f' f = Element (f (Abstract.Expression l f' f'))
                    | Range (f (Abstract.Expression l f' f')) (f (Abstract.Expression l f' f'))

deriving instance (Typeable l, Typeable f, Typeable f', Data (f (Abstract.Expression l f' f'))) => Data (Element l f' f)
deriving instance Show (f (Abstract.Expression l f' f')) => Show (Element l f' f)
deriving instance Eq (f (Abstract.Expression l f' f')) => Eq (Element l f' f)

data Designator l f' f = Variable (Abstract.QualIdent l)
                       | Field (f (Abstract.Designator l f' f')) Ident 
                       | Index (f (Abstract.Designator l f' f')) (NonEmpty (f (Abstract.Expression l f' f')))
                       | TypeGuard (f (Abstract.Designator l f' f')) (Abstract.QualIdent l)
                       | Dereference (f (Abstract.Designator l f' f'))

deriving instance (Data l, Typeable f, Typeable f', Data (Abstract.QualIdent l),
                   Data (f (Abstract.Designator l f' f')), Data (f (Abstract.Expression l f' f'))) =>
                  Data (Designator l f' f)
deriving instance (Show (Abstract.QualIdent l), Show (f (Abstract.Designator l f' f')),
                   Show (f (Abstract.Expression l f' f'))) => Show (Designator l f' f)
deriving instance (Eq (Abstract.QualIdent l), Eq (f (Abstract.Designator l f' f')),
                   Eq (f (Abstract.Expression l f' f'))) => Eq (Designator l f' f)

data Type l f' f = TypeReference (Abstract.QualIdent l)
                 | ArrayType [f (Abstract.ConstExpression l f' f')] (f (Abstract.Type l f' f'))
                 | RecordType (Maybe (Abstract.BaseType l)) (NonEmpty (f (Abstract.FieldList l f' f')))
                 | PointerType (f (Abstract.Type l f' f'))
                 | ProcedureType (Maybe (f (Abstract.FormalParameters l f' f')))

deriving instance (Data l, Typeable f, Typeable f', Data (Abstract.QualIdent l), Data (f (Abstract.Type l f' f')),
                   Data (f (Abstract.ConstExpression l f' f')), Data (f (Abstract.FormalParameters l f' f')),
                   Data (f (Abstract.FieldList l f' f'))) =>
                  Data (Type l f' f)
deriving instance (Show (Abstract.QualIdent l), Show (f (Abstract.Type l f' f')),
                   Show (f (Abstract.ConstExpression l f' f')), Show (f (Abstract.FormalParameters l f' f')),
                   Show (f (Abstract.FieldList l f' f'))) =>
                  Show (Type l f' f)

data FieldList l f' f = FieldList (Abstract.IdentList l) (f (Abstract.Type l f' f'))
                      | EmptyFieldList

deriving instance (Data l, Typeable f, Typeable f', Data (Abstract.IdentDef l), Data (f (Abstract.Type l f' f')),
                   Data (f (Abstract.Expression l f' f'))) => Data (FieldList l f' f)
deriving instance (Show (Abstract.IdentDef l), Show (f (Abstract.Type l f' f')), Show (f (Abstract.Expression l f' f'))) =>
                  Show (FieldList l f' f)

data ProcedureHeading l f' f =
   ProcedureHeading                    Bool (Abstract.IdentDef l) (Maybe (f (Abstract.FormalParameters l f' f')))
   | TypeBoundHeading Bool Ident Ident Bool (Abstract.IdentDef l) (Maybe (f (Abstract.FormalParameters l f' f')))

data FormalParameters l f' f = FormalParameters [f (Abstract.FPSection l f' f')] (Maybe (Abstract.ReturnType l))

data FPSection l f' f = FPSection Bool (NonEmpty Ident) (f (Abstract.Type l f' f'))

deriving instance (Data l, Typeable f, Typeable f', Data (Abstract.IdentDef l),
                   Data (f (Abstract.FormalParameters l f' f'))) => Data (ProcedureHeading l f' f)
deriving instance (Show (Abstract.IdentDef l), Show (f (Abstract.FormalParameters l f' f'))) =>
                  Show (ProcedureHeading l f' f)

deriving instance (Typeable l, Typeable f, Typeable f', Data (Abstract.ReturnType l),
                   Data (f (Abstract.FPSection l f' f')),  Data (f (Abstract.Expression l f' f'))) =>
                  Data (FormalParameters l f' f)
deriving instance (Show (f (Abstract.FPSection l f' f')), Show (Abstract.ReturnType l),
                   Show (f (Abstract.Expression l f' f'))) => Show (FormalParameters l f' f)

deriving instance (Typeable l, Typeable f, Typeable f', Data (f (Abstract.Type l f' f')),
                   Data (f (Abstract.Expression l f' f'))) => Data (FPSection l f' f)
deriving instance (Show (f (Abstract.Type l f' f')), Show (f (Abstract.Expression l f' f'))) => Show (FPSection l f' f)

data Block l f' f = Block [f (Abstract.Declaration l f' f')] (Maybe (f (Abstract.StatementSequence l f' f')))

deriving instance (Typeable l, Typeable f, Typeable f', Data (f (Abstract.Declaration l f' f')),
                   Data (f (Abstract.Designator l f' f')), Data (f (Abstract.Expression l f' f')),
                   Data (f (Abstract.StatementSequence l f' f'))) =>
                  Data (Block l f' f)
deriving instance (Show (f (Abstract.Declaration l f' f')), Show (f (Abstract.Designator l f' f')),
                   Show (f (Abstract.Expression l f' f')), Show (f (Abstract.StatementSequence l f' f'))) =>
                  Show (Block l f' f)

newtype StatementSequence l f' f = StatementSequence (NonEmpty (f (Abstract.Statement l f' f')))

deriving instance (Typeable l, Typeable f, Typeable f', Data (f (Abstract.Statement l f' f'))) =>
                  Data (StatementSequence l f' f)
deriving instance Show (f (Abstract.Statement l f' f')) => Show (StatementSequence l f' f)

data Statement l f' f = EmptyStatement
                      | Assignment (f (Abstract.Designator l f' f')) (f (Abstract.Expression l f' f'))
                      | ProcedureCall (f (Abstract.Designator l f' f')) (Maybe [f (Abstract.Expression l f' f')])
                      | If (NonEmpty (f (Product (Abstract.Expression l) (Abstract.StatementSequence l) f' f')))
                           (Maybe (f (Abstract.StatementSequence l f' f')))
                      | CaseStatement (f (Abstract.Expression l f' f')) 
                                      (NonEmpty (f (Abstract.Case l f' f'))) 
                                      (Maybe (f (Abstract.StatementSequence l f' f')))
                      | While (f (Abstract.Expression l f' f')) (f (Abstract.StatementSequence l f' f'))
                      | Repeat (f (Abstract.StatementSequence l f' f')) (f (Abstract.Expression l f' f'))
                      | For Ident (f (Abstract.Expression l f' f')) (f (Abstract.Expression l f' f')) 
                            (Maybe (f (Abstract.Expression l f' f'))) (f (Abstract.StatementSequence l f' f'))  -- Oberon2
                      | Loop (f (Abstract.StatementSequence l f' f'))
                      | With (NonEmpty (f (Abstract.WithAlternative l f' f')))
                             (Maybe (f (Abstract.StatementSequence l f' f')))
                      | Exit
                      | Return (Maybe (f (Abstract.Expression l f' f')))

deriving instance (Typeable l, Typeable f, Typeable f',
                   Data (f (Abstract.Designator l f' f')), Data (f (Abstract.Expression l f' f')),
                   Data (f (Product (Abstract.Expression l) (Abstract.StatementSequence l) f' f')),
                   Data (f (Abstract.Case l f' f')), Data (f (Abstract.WithAlternative l f' f')),
                   Data (f (Abstract.StatementSequence l f' f'))) => Data (Statement l f' f)
deriving instance (Show (f (Abstract.Designator l f' f')), Show (f (Abstract.Expression l f' f')),
                   Show (f (Product (Abstract.Expression l) (Abstract.StatementSequence l) f' f')),
                   Show (f (Abstract.Case l f' f')), Show (f (Abstract.WithAlternative l f' f')),
                   Show (f (Abstract.StatementSequence l f' f'))) => Show (Statement l f' f)

data WithAlternative l f' f = WithAlternative (Abstract.QualIdent l) (Abstract.QualIdent l)
                                              (f (Abstract.StatementSequence l f' f'))

data Case l f' f = Case (NonEmpty (f (Abstract.CaseLabels l f' f'))) (f (Abstract.StatementSequence l f' f'))
                 | EmptyCase

data CaseLabels l f' f = SingleLabel (f (Abstract.ConstExpression l f' f'))
                       | LabelRange (f (Abstract.ConstExpression l f' f')) (f (Abstract.ConstExpression l f' f'))

deriving instance (Typeable l, Typeable f, Typeable f', Data (Abstract.QualIdent l),
                   Data (f (Abstract.Designator l f' f')), Data (f (Abstract.StatementSequence l f' f'))) =>
                  Data (WithAlternative l f' f)
deriving instance (Show (Abstract.QualIdent l), Show (f (Abstract.StatementSequence l f' f'))) =>
                  Show (WithAlternative l f' f)

deriving instance (Typeable l, Typeable f, Typeable f', Show (Abstract.QualIdent l),
                   Data (f (Abstract.CaseLabels l f' f')), Data (f (Abstract.StatementSequence l f' f'))) =>
                  Data (Case l f' f)
deriving instance (Show (f (Abstract.CaseLabels l f' f')), Show (f (Abstract.StatementSequence l f' f'))) =>
                  Show (Case l f' f)

deriving instance (Typeable l, Typeable f, Typeable f', Data (f (Abstract.ConstExpression l f' f'))) =>
                  Data (CaseLabels l f' f)
deriving instance Show (f (Abstract.ConstExpression l f' f')) => Show (CaseLabels l f' f)

$(mconcat <$> mapM Transformation.Deep.TH.deriveAll
  [''Module, ''Declaration, ''Type, ''Expression,
   ''Element, ''Designator, ''FieldList,
   ''ProcedureHeading, ''FormalParameters, ''FPSection, ''Block,
   ''Statement, ''StatementSequence, ''WithAlternative, ''Case, ''CaseLabels])
