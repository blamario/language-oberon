{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances,
             StandaloneDeriving, TemplateHaskell, TypeFamilies #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}

-- | Oberon Abstract Syntax Tree definitions

module Language.Oberon.AST (module Language.Oberon.AST,
                            QualIdent(..), RelOp(..)) where

import Data.Data (Data, Typeable)
import Data.List.NonEmpty
import Data.Text (Text)

import Transformation.Deep (Product)
import qualified Transformation.Deep.TH
import qualified Rank2.TH

import qualified Language.Oberon.Abstract as Abstract
import Language.Oberon.Abstract (BaseType, QualIdent(..), RelOp(..))

data Language

instance Abstract.Oberon Language where
   type Module Language = Module
   type Declaration Language = Declaration
   type Type Language = Type
   type Statement Language = Statement
   type Expression Language = Expression
   type Designator Language = Designator

   type FieldList Language = FieldList
   type ProcedureHeading Language = ProcedureHeading
   type FormalParameters Language = FormalParameters
   type FPSection Language = FPSection
   type ProcedureBody Language = ProcedureBody
   type StatementSequence Language = StatementSequence
   type WithAlternative Language = WithAlternative
   type Case Language = Case
   type CaseLabels Language = CaseLabels
   type Element Language = Element

   type IdentDef Language = IdentDef
   type AccessMode Language = AccessMode

   moduleUnit = Module

   -- Declaration
   constantDeclaration = ConstantDeclaration
   typeDeclaration = TypeDeclaration
   variableDeclaration = VariableDeclaration
   procedureDeclaration = ProcedureDeclaration
   forwardDeclaration = ForwardDeclaration

   procedureHeading = ProcedureHeading
   formalParameters = FormalParameters
   fpSection = FPSection
   procedureBody = ProcedureBody
   
   identDef = IdentDef
   exported = Exported
   privateOnly = PrivateOnly

   fieldList = FieldList
   emptyFieldList = EmptyFieldList

   -- Type
   arrayType = ArrayType
   pointerType = PointerType
   procedureType = ProcedureType
   recordType = RecordType
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
   withStatement alt = With (alt :| []) Nothing

   withAlternative = WithAlternative
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
   charCode = CharCode
   charConstant = CharConstant
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
   set = Set
   string = String

   element = Element
   range = Range

   -- Designator
   variable = Variable
   field = Field
   index = Index
   typeGuard = TypeGuard
   dereference = Dereference

instance Abstract.Oberon2 Language where
   readOnly = ReadOnly
   typeBoundHeading = TypeBoundHeading
   forStatement = For
   variantWithStatement = With

data Module f' f = Module Ident [Import] [f (Declaration f' f')] (Maybe (f (StatementSequence f' f')))

deriving instance (Typeable f, Typeable f',
                   Data (f (Declaration f' f')), Data (f (StatementSequence f' f'))) => Data (Module f' f)
deriving instance (Show (f (Declaration f' f')), Show (f (StatementSequence f' f'))) => Show (Module f' f)

type Ident = Text

type Import = (Maybe Ident, Ident)

data Declaration f' f = ConstantDeclaration IdentDef (f (ConstExpression f' f'))
                      | TypeDeclaration IdentDef (f (Type f' f'))
                      | VariableDeclaration IdentList (f (Type f' f'))
                      | ProcedureDeclaration (f (ProcedureHeading f' f')) (ProcedureBody f' f)
                      | ForwardDeclaration IdentDef (Maybe (f (FormalParameters f' f')))

deriving instance (Typeable f, Typeable f',
                   Data (f (Type f' f')), Data (f (ConstExpression f' f')), Data (f (FormalParameters f' f')),
                   Data (f (ProcedureHeading f' f')), Data (ProcedureBody f' f)) => Data (Declaration f' f)
deriving instance (Show (f (Type f' f')), Show (f (ConstExpression f' f')), Show (f (FormalParameters f' f')),
                   Show (f (ProcedureHeading f' f')), Show (ProcedureBody f' f)) => Show (Declaration f' f)

data IdentDef = IdentDef Ident AccessMode
   deriving (Data, Eq, Ord, Show)

data AccessMode = Exported | ReadOnly | PrivateOnly
   deriving (Data, Eq, Ord, Show)

type ConstExpression = Expression

data Expression f' f = Relation RelOp (f (Expression f' f')) (f (Expression f' f'))
                     | Positive (f (Expression f' f'))
                     | Negative (f (Expression f' f'))
                     | Add (f (Expression f' f')) (f (Expression f' f'))
                     | Subtract (f (Expression f' f')) (f (Expression f' f'))
                     | Or (f (Expression f' f')) (f (Expression f' f'))
                     | Multiply (f (Expression f' f')) (f (Expression f' f'))
                     | Divide (f (Expression f' f')) (f (Expression f' f'))
                     | IntegerDivide (f (Expression f' f')) (f (Expression f' f'))
                     | Modulo (f (Expression f' f')) (f (Expression f' f'))
                     | And (f (Expression f' f')) (f (Expression f' f'))
                     | Integer Text
                     | Real Text
                     | CharConstant Char
                     | CharCode Int
                     | String Text
                     | Nil 
                     | Set [f (Element f' f')]
                     | Read (f (Designator f' f'))
                     | FunctionCall (f (Designator f' f')) [f (Expression f' f')]
                     | Not (f (Expression f' f'))

deriving instance (Typeable f, Typeable f', Data (f (Designator f' f')),
                   Data (f (Element f' f')), Data (f (Expression f' f'))) => Data (Expression f' f)
deriving instance (Show (f (Designator f' f')),
                   Show (f (Element f' f')), Show (f (Expression f' f'))) => Show (Expression f' f)
deriving instance (Eq (f (Designator f' f')), Eq (f (Element f' f')), Eq (f (Expression f' f'))) => Eq (Expression f' f)

data Element f' f = Element (f (Expression f' f'))
                  | Range (f (Expression f' f')) (f (Expression f' f'))

deriving instance (Typeable f, Typeable f', Data (f (Expression f' f'))) => Data (Element f' f)
deriving instance Show (f (Expression f' f')) => Show (Element f' f)
deriving instance Eq (f (Expression f' f')) => Eq (Element f' f)

data Designator f' f = Variable QualIdent
                     | Field (f (Designator f' f')) Ident 
                     | Index (f (Designator f' f')) (NonEmpty (f (Expression f' f')))
                     | TypeGuard (f (Designator f' f')) QualIdent 
                     | Dereference (f (Designator f' f'))

deriving instance (Typeable f, Typeable f', Data (f (Designator f' f')), Data (f (Expression f' f'))) =>
                  Data (Designator f' f)
deriving instance (Show (f (Designator f' f')), Show (f (Expression f' f'))) => Show (Designator f' f)
deriving instance (Eq (f (Designator f' f')), Eq (f (Expression f' f'))) => Eq (Designator f' f)

data Type f' f = TypeReference QualIdent 
               | ArrayType [f (ConstExpression f' f')] (f (Type f' f'))
               | RecordType (Maybe BaseType) (NonEmpty (f (FieldList f' f')))
               | PointerType (f (Type f' f'))
               | ProcedureType (Maybe (f (FormalParameters f' f')))

deriving instance (Typeable f, Typeable f', Data (f (Type f' f')), Data (f (ConstExpression f' f')),
                   Data (f (FormalParameters f' f')), Data (f (FieldList f' f'))) => Data (Type f' f)
deriving instance (Show (f (Type f' f')), Show (f (ConstExpression f' f')),
                   Show (f (FormalParameters f' f')), Show (f (FieldList f' f'))) => Show (Type f' f)

data FieldList f' f = FieldList IdentList (f (Type f' f'))
                    | EmptyFieldList

deriving instance (Typeable f, Typeable f', Data (f (Type f' f')), Data (f (Expression f' f'))) => Data (FieldList f' f)
deriving instance (Show (f (Type f' f')), Show (f (Expression f' f'))) => Show (FieldList f' f)

type IdentList = NonEmpty IdentDef

data ProcedureHeading f' f = ProcedureHeading                  Bool IdentDef (Maybe (f (FormalParameters f' f')))
                           | TypeBoundHeading Bool Ident Ident Bool IdentDef (Maybe (f (FormalParameters f' f')))

data FormalParameters f' f = FormalParameters [f (FPSection f' f')] (Maybe QualIdent)

data FPSection f' f = FPSection Bool (NonEmpty Ident) (f (Type f' f'))

deriving instance (Typeable f, Typeable f', Data (f (FormalParameters f' f'))) => Data (ProcedureHeading f' f)
deriving instance (Show (f (FormalParameters f' f'))) => Show (ProcedureHeading f' f)

deriving instance (Typeable f, Typeable f', Data (f (FPSection f' f')),  Data (f (Expression f' f'))) =>
                  Data (FormalParameters f' f)
deriving instance (Show (f (FPSection f' f')), Show (f (Expression f' f'))) => Show (FormalParameters f' f)

deriving instance (Typeable f, Typeable f', Data (f (Type f' f')),  Data (f (Expression f' f'))) =>
                  Data (FPSection f' f)
deriving instance (Show (f (Type f' f')), Show (f (Expression f' f'))) => Show (FPSection f' f)

data ProcedureBody f' f =  ProcedureBody [f (Declaration f' f')] (Maybe (f (StatementSequence f' f')))

deriving instance (Typeable f, Typeable f', Data (f (Declaration f' f')), Data (f (Designator f' f')),
                   Data (f (Expression f' f')), Data (f (StatementSequence f' f'))) =>
                  Data (ProcedureBody f' f)
deriving instance (Show (f (Declaration f' f')), Show (f (Designator f' f')),
                   Show (f (Expression f' f')), Show (f (StatementSequence f' f'))) => Show (ProcedureBody f' f)

newtype StatementSequence f' f = StatementSequence (NonEmpty (f (Statement f' f')))

deriving instance (Typeable f, Typeable f', Data (f (Statement f' f'))) => Data (StatementSequence f' f)
deriving instance Show (f (Statement f' f')) => Show (StatementSequence f' f)

data Statement f' f = EmptyStatement
                    | Assignment (f (Designator f' f')) (f (Expression f' f'))
                    | ProcedureCall (f (Designator f' f')) (Maybe [f (Expression f' f')])
                    | If (NonEmpty (f (Product Expression StatementSequence f' f')))
                         (Maybe (f (StatementSequence f' f')))
                    | CaseStatement (f (Expression f' f')) 
                                    (NonEmpty (f (Case f' f'))) 
                                    (Maybe (f (StatementSequence f' f')))
                    | While (f (Expression f' f')) (f (StatementSequence f' f'))
                    | Repeat (f (StatementSequence f' f')) (f (Expression f' f'))
                    | For Ident (f (Expression f' f')) (f (Expression f' f')) 
                          (Maybe (f (Expression f' f'))) (f (StatementSequence f' f'))  -- Oberon2
                    | Loop (f (StatementSequence f' f'))
                    | With (NonEmpty (f (WithAlternative f' f'))) (Maybe (f (StatementSequence f' f')))
                    | Exit
                    | Return (Maybe (f (Expression f' f')))

deriving instance (Typeable f, Typeable f', Data (f (Designator f' f')), Data (f (Expression f' f')),
                   Data (f (Product Expression StatementSequence f' f')),
                   Data (f (Case f' f')), Data (f (WithAlternative f' f')),
                   Data (f (Statement f' f')), Data (f (StatementSequence f' f'))) => Data (Statement f' f)
deriving instance (Show (f (Designator f' f')), Show (f (Expression f' f')),
                   Show (f (Product Expression StatementSequence f' f')),
                   Show (f (Case f' f')), Show (f (WithAlternative f' f')),
                   Show (f (Statement f' f')), Show (f (StatementSequence f' f'))) => Show (Statement f' f)

data WithAlternative f' f = WithAlternative QualIdent QualIdent (f (StatementSequence f' f'))

data Case f' f = Case (NonEmpty (f (CaseLabels f' f'))) (f (StatementSequence f' f'))
               | EmptyCase

data CaseLabels f' f = SingleLabel (f (ConstExpression f' f'))
                     | LabelRange (f (ConstExpression f' f')) (f (ConstExpression f' f'))

deriving instance (Typeable f, Typeable f', Data (f (Designator f' f')), Data (f (StatementSequence f' f'))) =>
                  Data (WithAlternative f' f)
deriving instance (Show (f (StatementSequence f' f'))) => Show (WithAlternative f' f)

deriving instance (Typeable f, Typeable f', Data (f (CaseLabels f' f')), Data (f (StatementSequence f' f'))) =>
                  Data (Case f' f)
deriving instance (Show (f (CaseLabels f' f')), Show (f (StatementSequence f' f'))) => Show (Case f' f)

deriving instance (Typeable f, Typeable f', Data (f (ConstExpression f' f'))) => Data (CaseLabels f' f)
deriving instance Show (f (ConstExpression f' f')) => Show (CaseLabels f' f)

$(mconcat <$> mapM Transformation.Deep.TH.deriveAll
  [''Module, ''Declaration, ''Type, ''Expression,
   ''Element, ''Designator, ''FieldList,
   ''ProcedureHeading, ''FormalParameters, ''FPSection, ''ProcedureBody,
   ''Statement, ''StatementSequence, ''WithAlternative, ''Case, ''CaseLabels])
