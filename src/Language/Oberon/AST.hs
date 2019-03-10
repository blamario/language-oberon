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

data Language deriving (Data, Typeable)

instance Abstract.Wirthy Language where
   type Module Language = Module Language
   type Declaration Language = Declaration Language
   type Type Language = Type Language
   type Statement Language = Statement Language
   type Expression Language = Expression Language
   type Designator Language = Designator Language

   type FieldList Language = FieldList Language
   type ProcedureHeading Language = ProcedureHeading Language
   type FormalParameters Language = FormalParameters Language
   type FPSection Language = FPSection Language
   type ProcedureBody Language = ProcedureBody Language
   type StatementSequence Language = StatementSequence Language
   type WithAlternative Language = WithAlternative Language
   type Case Language = Case Language
   type CaseLabels Language = CaseLabels Language
   type Element Language = Element Language

   type IdentDef Language = IdentDef Language

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
   
   identDef = flip IdentDef PrivateOnly

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

instance Abstract.Nameable Language where
   getProcedureName (ProcedureHeading _ iddef _) = Abstract.getIdentDefName iddef
   getProcedureName (TypeBoundHeading _ _ _ _ iddef _) = Abstract.getIdentDefName iddef
   getIdentDefName (IdentDef name _) = name

instance Abstract.Oberon Language where
   exported = flip IdentDef Exported
   is = IsA

instance Abstract.Oberon2 Language where
   readOnly = flip IdentDef ReadOnly
   typeBoundHeading = TypeBoundHeading
   forStatement = For
   variantWithStatement = With

data Module l f' f = Module Ident [Import] [f (Abstract.Declaration l f' f')] (Maybe (f (StatementSequence l f' f')))

deriving instance (Typeable l, Typeable f, Typeable f',
                   Data (f (Abstract.Declaration l f' f')), Data (f (StatementSequence l f' f'))) => Data (Module l f' f)
deriving instance (Show (f (Abstract.Declaration l f' f')), Show (f (StatementSequence l f' f'))) => Show (Module l f' f)

type Ident = Text

type Import = (Maybe Ident, Ident)

data Declaration l f' f = ConstantDeclaration (Abstract.IdentDef l) (f (ConstExpression l f' f'))
                        | TypeDeclaration (Abstract.IdentDef l) (f (Abstract.Type l f' f'))
                        | VariableDeclaration (IdentList l) (f (Abstract.Type l f' f'))
                        | ProcedureDeclaration (f (Abstract.ProcedureHeading l f' f')) (ProcedureBody l f' f)
                        | ForwardDeclaration (Abstract.IdentDef l) (Maybe (f (Abstract.FormalParameters l f' f')))

deriving instance (Data l, Typeable f, Typeable f',
                   Data (f (Abstract.Type l f' f')), Data (f (ConstExpression l f' f')),
                   Data (f (Abstract.FormalParameters l f' f')), Data (f (Abstract.ProcedureHeading l f' f')),
                   Data (ProcedureBody l f' f), Data (Abstract.IdentDef l)) => Data (Declaration l f' f)
deriving instance (Show (f (Abstract.Type l f' f')), Show (f (ConstExpression l f' f')),
                   Show (f (Abstract.FormalParameters l f' f')), Show (f (Abstract.ProcedureHeading l f' f')),
                   Show (ProcedureBody l f' f), Show (Abstract.IdentDef l)) => Show (Declaration l f' f)

data IdentDef l = IdentDef Ident AccessMode
   deriving (Data, Eq, Ord, Show)

data AccessMode = Exported | ReadOnly | PrivateOnly
   deriving (Data, Eq, Ord, Show)

type ConstExpression = Expression

data Expression l f' f = Relation RelOp (f (Expression l f' f')) (f (Expression l f' f'))
                       | IsA (f (Expression l f' f')) QualIdent
                       | Positive (f (Expression l f' f'))
                       | Negative (f (Expression l f' f'))
                       | Add (f (Expression l f' f')) (f (Expression l f' f'))
                       | Subtract (f (Expression l f' f')) (f (Expression l f' f'))
                       | Or (f (Expression l f' f')) (f (Expression l f' f'))
                       | Multiply (f (Expression l f' f')) (f (Expression l f' f'))
                       | Divide (f (Expression l f' f')) (f (Expression l f' f'))
                       | IntegerDivide (f (Expression l f' f')) (f (Expression l f' f'))
                       | Modulo (f (Expression l f' f')) (f (Expression l f' f'))
                       | And (f (Expression l f' f')) (f (Expression l f' f'))
                       | Integer Text
                       | Real Text
                       | CharConstant Char
                       | CharCode Int
                       | String Text
                       | Nil 
                       | Set [f (Element l f' f')]
                       | Read (f (Designator l f' f'))
                       | FunctionCall (f (Designator l f' f')) [f (Expression l f' f')]
                       | Not (f (Expression l f' f'))

deriving instance (Typeable l, Typeable f, Typeable f', Data (f (Designator l f' f')),
                   Data (f (Element l f' f')), Data (f (Expression l f' f'))) => Data (Expression l f' f)
deriving instance (Show (f (Designator l f' f')),
                   Show (f (Element l f' f')), Show (f (Expression l f' f'))) => Show (Expression l f' f)
deriving instance (Eq (f (Designator l f' f')), Eq (f (Element l f' f')), Eq (f (Expression l f' f'))) => Eq (Expression l f' f)

data Element l f' f = Element (f (Expression l f' f'))
                    | Range (f (Expression l f' f')) (f (Expression l f' f'))

deriving instance (Typeable l, Typeable f, Typeable f', Data (f (Expression l f' f'))) => Data (Element l f' f)
deriving instance Show (f (Expression l f' f')) => Show (Element l f' f)
deriving instance Eq (f (Expression l f' f')) => Eq (Element l f' f)

data Designator l f' f = Variable QualIdent
                       | Field (f (Designator l f' f')) Ident 
                       | Index (f (Designator l f' f')) (NonEmpty (f (Expression l f' f')))
                       | TypeGuard (f (Designator l f' f')) QualIdent 
                       | Dereference (f (Designator l f' f'))

deriving instance (Typeable l, Typeable f, Typeable f', Data (f (Designator l f' f')), Data (f (Expression l f' f'))) =>
                  Data (Designator l f' f)
deriving instance (Show (f (Designator l f' f')), Show (f (Expression l f' f'))) => Show (Designator l f' f)
deriving instance (Eq (f (Designator l f' f')), Eq (f (Expression l f' f'))) => Eq (Designator l f' f)

data Type l f' f = TypeReference QualIdent 
                 | ArrayType [f (ConstExpression l f' f')] (f (Abstract.Type l f' f'))
                 | RecordType (Maybe BaseType) (NonEmpty (f (Abstract.FieldList l f' f')))
                 | PointerType (f (Abstract.Type l f' f'))
                 | ProcedureType (Maybe (f (Abstract.FormalParameters l f' f')))

deriving instance (Typeable l, Typeable f, Typeable f', Data (f (Abstract.Type l f' f')), Data (f (ConstExpression l f' f')),
                   Data (f (Abstract.FormalParameters l f' f')), Data (f (Abstract.FieldList l f' f'))) => Data (Type l f' f)
deriving instance (Show (f (Abstract.Type l f' f')), Show (f (ConstExpression l f' f')),
                   Show (f (Abstract.FormalParameters l f' f')), Show (f (Abstract.FieldList l f' f'))) => Show (Type l f' f)

data FieldList l f' f = FieldList (IdentList l) (f (Abstract.Type l f' f'))
                      | EmptyFieldList

deriving instance (Data l, Typeable f, Typeable f', Data (Abstract.IdentDef l), Data (f (Abstract.Type l f' f')),
                   Data (f (Expression l f' f'))) => Data (FieldList l f' f)
deriving instance (Show (Abstract.IdentDef l), Show (f (Abstract.Type l f' f')), Show (f (Expression l f' f'))) =>
                  Show (FieldList l f' f)

type IdentList l = NonEmpty (Abstract.IdentDef l)

data ProcedureHeading l f' f =
   ProcedureHeading                    Bool (Abstract.IdentDef l) (Maybe (f (Abstract.FormalParameters l f' f')))
   | TypeBoundHeading Bool Ident Ident Bool (Abstract.IdentDef l) (Maybe (f (Abstract.FormalParameters l f' f')))

data FormalParameters l f' f = FormalParameters [f (FPSection l f' f')] (Maybe QualIdent)

data FPSection l f' f = FPSection Bool (NonEmpty Ident) (f (Abstract.Type l f' f'))

deriving instance (Data l, Typeable f, Typeable f', Data (Abstract.IdentDef l),
                   Data (f (Abstract.FormalParameters l f' f'))) => Data (ProcedureHeading l f' f)
deriving instance (Show (Abstract.IdentDef l), Show (f (Abstract.FormalParameters l f' f'))) =>
                  Show (ProcedureHeading l f' f)

deriving instance (Typeable l, Typeable f, Typeable f', Data (f (FPSection l f' f')),  Data (f (Expression l f' f'))) =>
                  Data (FormalParameters l f' f)
deriving instance (Show (f (FPSection l f' f')), Show (f (Expression l f' f'))) => Show (FormalParameters l f' f)

deriving instance (Typeable l, Typeable f, Typeable f', Data (f (Abstract.Type l f' f')),
                   Data (f (Expression l f' f'))) => Data (FPSection l f' f)
deriving instance (Show (f (Abstract.Type l f' f')), Show (f (Expression l f' f'))) => Show (FPSection l f' f)

data ProcedureBody l f' f =  ProcedureBody [f (Abstract.Declaration l f' f')] (Maybe (f (StatementSequence l f' f')))

deriving instance (Typeable l, Typeable f, Typeable f', Data (f (Abstract.Declaration l f' f')), Data (f (Designator l f' f')),
                   Data (f (Expression l f' f')), Data (f (StatementSequence l f' f'))) =>
                  Data (ProcedureBody l f' f)
deriving instance (Show (f (Abstract.Declaration l f' f')), Show (f (Designator l f' f')),
                   Show (f (Expression l f' f')), Show (f (StatementSequence l f' f'))) => Show (ProcedureBody l f' f)

newtype StatementSequence l f' f = StatementSequence (NonEmpty (f (Statement l f' f')))

deriving instance (Typeable l, Typeable f, Typeable f', Data (f (Statement l f' f'))) => Data (StatementSequence l f' f)
deriving instance Show (f (Statement l f' f')) => Show (StatementSequence l f' f)

data Statement l f' f = EmptyStatement
                      | Assignment (f (Designator l f' f')) (f (Expression l f' f'))
                      | ProcedureCall (f (Designator l f' f')) (Maybe [f (Expression l f' f')])
                      | If (NonEmpty (f (Product (Expression l) (StatementSequence l) f' f')))
                           (Maybe (f (StatementSequence l f' f')))
                      | CaseStatement (f (Expression l f' f')) 
                                      (NonEmpty (f (Case l f' f'))) 
                                      (Maybe (f (StatementSequence l f' f')))
                      | While (f (Expression l f' f')) (f (StatementSequence l f' f'))
                      | Repeat (f (StatementSequence l f' f')) (f (Expression l f' f'))
                      | For Ident (f (Expression l f' f')) (f (Expression l f' f')) 
                            (Maybe (f (Expression l f' f'))) (f (StatementSequence l f' f'))  -- Oberon2
                      | Loop (f (StatementSequence l f' f'))
                      | With (NonEmpty (f (WithAlternative l f' f'))) (Maybe (f (StatementSequence l f' f')))
                      | Exit
                      | Return (Maybe (f (Expression l f' f')))

deriving instance (Typeable l, Typeable f, Typeable f', Data (f (Designator l f' f')), Data (f (Expression l f' f')),
                   Data (f (Product (Expression l) (StatementSequence l) f' f')),
                   Data (f (Case l f' f')), Data (f (WithAlternative l f' f')),
                   Data (f (Statement l f' f')), Data (f (StatementSequence l f' f'))) => Data (Statement l f' f)
deriving instance (Show (f (Designator l f' f')), Show (f (Expression l f' f')),
                   Show (f (Product (Expression l) (StatementSequence l) f' f')),
                   Show (f (Case l f' f')), Show (f (WithAlternative l f' f')),
                   Show (f (Statement l f' f')), Show (f (StatementSequence l f' f'))) => Show (Statement l f' f)

data WithAlternative l f' f = WithAlternative QualIdent QualIdent (f (StatementSequence l f' f'))

data Case l f' f = Case (NonEmpty (f (CaseLabels l f' f'))) (f (StatementSequence l f' f'))
                 | EmptyCase

data CaseLabels l f' f = SingleLabel (f (ConstExpression l f' f'))
                       | LabelRange (f (ConstExpression l f' f')) (f (ConstExpression l f' f'))

deriving instance (Typeable l, Typeable f, Typeable f', Data (f (Designator l f' f')), Data (f (StatementSequence l f' f'))) =>
                  Data (WithAlternative l f' f)
deriving instance (Show (f (StatementSequence l f' f'))) => Show (WithAlternative l f' f)

deriving instance (Typeable l, Typeable f, Typeable f', Data (f (CaseLabels l f' f')), Data (f (StatementSequence l f' f'))) =>
                  Data (Case l f' f)
deriving instance (Show (f (CaseLabels l f' f')), Show (f (StatementSequence l f' f'))) => Show (Case l f' f)

deriving instance (Typeable l, Typeable f, Typeable f', Data (f (ConstExpression l f' f'))) => Data (CaseLabels l f' f)
deriving instance Show (f (ConstExpression l f' f')) => Show (CaseLabels l f' f)

$(mconcat <$> mapM Transformation.Deep.TH.deriveAll
  [''Module, ''Declaration, ''Type, ''Expression,
   ''Element, ''Designator, ''FieldList,
   ''ProcedureHeading, ''FormalParameters, ''FPSection, ''ProcedureBody,
   ''Statement, ''StatementSequence, ''WithAlternative, ''Case, ''CaseLabels])
