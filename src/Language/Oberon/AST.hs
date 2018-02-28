{-# LANGUAGE DeriveDataTypeable #-}

module Language.Oberon.AST where

import Data.Data (Data)
import Data.List.NonEmpty
import Data.Text
import Text.Grampa (Ambiguous)

data Module = Module Ident [Import] [Declaration] (Maybe StatementSequence) Ident
   deriving (Data, Show)

type Ident = Text

data Import = Import Ident (Maybe Ident)
   deriving (Data, Show)

data Declaration  = ConstantDeclaration IdentDef ConstExpression
                  | TypeDeclaration IdentDef Type
                  | VariableDeclaration IdentList Type
                  | ProcedureDeclaration ProcedureHeading ProcedureBody Ident
                  | ForwardDeclaration Ident Bool (Maybe FormalParameters) 
   deriving (Data, Show)

data IdentDef = IdentDef Ident Bool
   deriving (Data, Show)

type ConstExpression = Expression

data Expression = Relation RelOp Expression Expression
                | Positive Expression
                | Negative Expression
                | Add Expression Expression
                | Subtract Expression Expression
                | Or Expression Expression
                | Multiply Expression Expression
                | Divide Expression Expression
                | IntegerDivide Expression Expression
                | Modulo Expression Expression
                | And Expression Expression
                | Integer Text
                | Real Text
                | CharConstant Char
                | CharCode Int
                | String Text
                | Nil 
                | BooleanConstant Bool
                | Set [Element]
                | Read AmbDesignator
                | FunctionCall AmbDesignator ActualParameters
                | Not Expression
   deriving (Data, Show)

data RelOp = Equal | Unequal | Less | LessOrEqual | Greater | GreaterOrEqual | In | Is
   deriving (Data, Show)

data Element = Element Expression
             | Range Expression Expression
   deriving (Data, Show)

type AmbDesignator = Ambiguous Designator

data Designator = Variable QualIdent
                | Field Designator Ident 
                | Index Designator (NonEmpty Expression) 
                | TypeGuard Designator QualIdent 
                | Dereference Designator
   deriving (Data, Show)

type ActualParameters = [Expression]

data Type = TypeReference QualIdent 
          | ArrayType (NonEmpty Length) Type 
          | RecordType (Maybe BaseType) FieldListSequence
          | PointerType Type
          | ProcedureType (Maybe FormalParameters)
   deriving (Data, Show)

data QualIdent = QualIdent Ident Ident 
               | NonQualIdent Ident
   deriving (Data, Show)

type Length  =  ConstExpression

type BaseType  =  QualIdent

type FieldListSequence = [FieldList]

data FieldList = FieldList IdentList Type
   deriving (Data, Show)

type IdentList = NonEmpty IdentDef

data ProcedureHeading  =  ProcedureHeading Bool IdentDef (Maybe FormalParameters)
   deriving (Data, Show)

data FormalParameters  = FormalParameters [FPSection] (Maybe QualIdent)
   deriving (Data, Show)
data FPSection  =  FPSection Bool (NonEmpty Ident) FormalType
   deriving (Data, Show)

data FormalType  = ArrayOf FormalType
                 | FormalTypeReference QualIdent 
                 | FormalProcedureType (Maybe FormalParameters)
   deriving (Data, Show)

data ProcedureBody  =  ProcedureBody [Declaration] (Maybe StatementSequence)
   deriving (Data, Show)

type StatementSequence  = [Ambiguous Statement]

data Statement = EmptyStatement
               | Assignment Designator Expression 
               | ProcedureCall Designator (Maybe ActualParameters)
               | If Expression StatementSequence [(Expression, StatementSequence)] (Maybe StatementSequence)
               | CaseStatement Expression (NonEmpty (Maybe Case)) (Maybe StatementSequence)
               | While Expression StatementSequence
               | Repeat StatementSequence Expression
               | For Ident Expression Expression (Maybe Expression) StatementSequence  -- Oberon2
               | Loop StatementSequence
               | With QualIdent QualIdent StatementSequence
               | Exit 
               | Return (Maybe Expression)
   deriving (Data, Show)

data Case = Case (NonEmpty CaseLabels) StatementSequence
   deriving (Data, Show)
data CaseLabels = SingleLabel ConstExpression 
                | LabelRange ConstExpression  ConstExpression
   deriving (Data, Show)
