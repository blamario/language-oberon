
module Language.Oberon.AST where

import Data.List.NonEmpty
import Data.Text

data Module = Module Ident [Import] [Declaration] (Maybe StatementSequence) Ident

type Ident = Text

data Import = Import Ident (Maybe Ident)

data Declaration  = ConstantDeclaration IdentDef ConstExpression
                  | TypeDeclaration IdentDef Type
                  | VariableDeclaration IdentList Type
                  | ProcedureDeclaration ProcedureHeading ProcedureBody Ident
                  | ForwardDeclaration Ident Bool (Maybe FormalParameters) 

data IdentDef = IdentDef Ident Bool

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
                | Set [Element]
                | Read Designator
                | FunctionCall Designator ActualParameters
                | Negate Expression

data RelOp = Equal | Unequal | Less | LessOrEqual | Greater | GreaterOrEqual | In | Is

data Element = Element Expression
             | Range Expression Expression

data Designator = Variable QualIdent
                | Field Designator Ident 
                | Index Designator (NonEmpty Expression) 
                | TypeGuard Designator QualIdent 
                | Dereference Designator

type ActualParameters = [Expression]

data Type = TypeReference QualIdent 
          | ArrayType (NonEmpty Length) Type 
          | RecordType (Maybe BaseType) FieldListSequence
          | PointerType Type
          | ProcedureType (Maybe FormalParameters)

data QualIdent = QualIdent Ident Ident 
               | NonQualIdent Ident

type Length  =  ConstExpression

type BaseType  =  QualIdent

type FieldListSequence = [FieldList]

data FieldList = FieldList IdentList Type

type IdentList = NonEmpty IdentDef

data ProcedureHeading  =  ProcedureHeading Bool IdentDef (Maybe FormalParameters)

data FormalParameters  = FormalParameters [FPSection] (Maybe QualIdent)
data FPSection  =  FPSection Bool (NonEmpty Ident) FormalType

data FormalType  = ArrayOf FormalType
                 | FormalTypeReference QualIdent 
                 | FormalProcedureType (Maybe FormalParameters)

data ProcedureBody  =  ProcedureBody [Declaration] (Maybe StatementSequence)

type StatementSequence  =  [Statement]

data Statement = Assignment Designator Expression 
               | ProcedureCall Designator (Maybe ActualParameters)
               | If Expression StatementSequence [(Expression, StatementSequence)] (Maybe StatementSequence)
               | CaseStatement Expression (NonEmpty (Maybe Case)) (Maybe StatementSequence)
               | While Expression StatementSequence
               | Repeat StatementSequence Expression
               | Loop StatementSequence
               | With QualIdent QualIdent StatementSequence
               | Exit 
               | Return (Maybe Expression)

data Case = Case (NonEmpty CaseLabels) StatementSequence
data CaseLabels = SingleLabel ConstExpression 
                | LabelRange ConstExpression  ConstExpression
