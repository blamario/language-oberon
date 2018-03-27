{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, UndecidableInstances, StandaloneDeriving #-}

module Language.Oberon.AST where

import Data.Data (Data)
import Data.Functor.Identity (Identity)
import Data.List.NonEmpty
import Data.Text
import Text.Grampa (Ambiguous)

data Module f = Module Ident [Import] [Declaration f] (Maybe (StatementSequence f)) Ident

deriving instance Data (Module Identity)
deriving instance Data (Module Ambiguous)
deriving instance (Show (f (Designator f)), Show (f (Statement f))) => Show (Module f)

type Ident = Text

type Import = (Maybe Ident, Ident)

data Declaration f  = ConstantDeclaration IdentDef (ConstExpression f)
                    | TypeDeclaration IdentDef (Type f)
                    | VariableDeclaration IdentList (Type f)
                    | ProcedureDeclaration (ProcedureHeading f) (ProcedureBody f) Ident
                    | ForwardDeclaration IdentDef (Maybe (FormalParameters f))

deriving instance Data (Declaration Identity)
deriving instance Data (Declaration Ambiguous)
deriving instance (Show (f (Designator f)), Show (f (Statement f))) => Show (Declaration f)

data IdentDef = IdentDef Ident AccessMode
   deriving (Data, Show)

data AccessMode = Exported | ReadOnly | PrivateOnly
   deriving (Data, Show)

type ConstExpression = Expression

data Expression f = Relation RelOp (Expression f) (Expression f)
                  | Positive (Expression f)
                  | Negative (Expression f)
                  | Add (Expression f) (Expression f)
                  | Subtract (Expression f) (Expression f)
                  | Or (Expression f) (Expression f)
                  | Multiply (Expression f) (Expression f)
                  | Divide (Expression f) (Expression f)
                  | IntegerDivide (Expression f) (Expression f)
                  | Modulo (Expression f) (Expression f)
                  | And (Expression f) (Expression f)
                  | Integer Text
                  | Real Text
                  | CharConstant Char
                  | CharCode Int
                  | String Text
                  | Nil 
                  | Set [Element f]
                  | Read (AmbDesignator f)
                  | FunctionCall (AmbDesignator f) (ActualParameters f)
                  | Not (Expression f)

deriving instance Data (Expression Identity)
deriving instance Data (Expression Ambiguous)
deriving instance Show (f (Designator f)) => Show (Expression f)

data RelOp = Equal | Unequal | Less | LessOrEqual | Greater | GreaterOrEqual | In | Is
   deriving (Data, Show)

data Element f = Element (Expression f)
               | Range (Expression f) (Expression f)

deriving instance Data (Element Identity)
deriving instance Data (Element Ambiguous)
deriving instance Show (f (Designator f)) => Show (Element f)

type AmbDesignator f = f (Designator f)

data Designator f = Variable QualIdent
                  | Field (Designator f) Ident 
                  | Index (Designator f) (NonEmpty (Expression f))
                  | TypeGuard (Designator f) QualIdent 
                  | Dereference (Designator f)

deriving instance Data (Designator Identity)
deriving instance Data (Designator Ambiguous)
deriving instance Show (f (Designator f)) => Show (Designator f)

type ActualParameters f = [Expression f]

data Type f = TypeReference QualIdent 
            | ArrayType [ConstExpression f] (Type f)
            | RecordType (Maybe BaseType) (FieldListSequence f)
            | PointerType (Type f)
            | ProcedureType (Maybe (FormalParameters f))

deriving instance Data (Type Identity)
deriving instance Data (Type Ambiguous)
deriving instance Show (f (Designator f)) => Show (Type f)

data QualIdent = QualIdent Ident Ident 
               | NonQualIdent Ident
   deriving (Data, Show)

type BaseType  =  QualIdent

type FieldListSequence f = [FieldList f]

data FieldList f = FieldList IdentList (Type f)

deriving instance Data (FieldList Identity)
deriving instance Data (FieldList Ambiguous)
deriving instance Show (f (Designator f)) => Show (FieldList f)

type IdentList = NonEmpty IdentDef

data ProcedureHeading f =  ProcedureHeading (Maybe (Bool, Ident, Ident)) Bool IdentDef (Maybe (FormalParameters f))
data FormalParameters f  = FormalParameters [FPSection f] (Maybe QualIdent)
data FPSection f  =  FPSection Bool (NonEmpty Ident) (Type f)

deriving instance Data (ProcedureHeading Identity)
deriving instance Data (ProcedureHeading Ambiguous)
deriving instance Show (f (Designator f)) => Show (ProcedureHeading f)

deriving instance Data (FormalParameters Identity)
deriving instance Data (FormalParameters Ambiguous)
deriving instance Show (f (Designator f)) => Show (FormalParameters f)

deriving instance Data (FPSection Identity)
deriving instance Data (FPSection Ambiguous)
deriving instance Show (f (Designator f)) => Show (FPSection f)

data ProcedureBody f =  ProcedureBody [Declaration f] (Maybe (StatementSequence f))

deriving instance Data (ProcedureBody Identity)
deriving instance Data (ProcedureBody Ambiguous)
deriving instance (Show (f (Designator f)), Show (f (Statement f))) => Show (ProcedureBody f)

type StatementSequence f  = [f (Statement f)]

data Statement f = EmptyStatement
                 | Assignment (AmbDesignator f) (Expression f)
                 | ProcedureCall (AmbDesignator f) (Maybe (ActualParameters f))
                 | If (NonEmpty (Expression f, StatementSequence f)) (Maybe (StatementSequence f))
                 | CaseStatement (Expression f) [Case f] (Maybe (StatementSequence f))
                 | While (Expression f) (StatementSequence f)
                 | Repeat (StatementSequence f) (Expression f)
                 | For Ident (Expression f) (Expression f) (Maybe (Expression f)) (StatementSequence f)  -- Oberon2
                 | Loop (StatementSequence f)
                 | With (NonEmpty (WithAlternative f)) (Maybe (StatementSequence f))
                 | Exit 
                 | Return (Maybe (Expression f))

deriving instance Data (Statement Identity)
deriving instance Data (Statement Ambiguous)
deriving instance (Show (f (Designator f)), Show (f (Statement f))) => Show (Statement f)

data WithAlternative f = WithAlternative QualIdent QualIdent (StatementSequence f)

data Case f = Case (NonEmpty (CaseLabels f)) (StatementSequence f)

data CaseLabels f = SingleLabel (ConstExpression f)
                  | LabelRange (ConstExpression f) (ConstExpression f)

deriving instance Data (WithAlternative Identity)
deriving instance Data (WithAlternative Ambiguous)
deriving instance (Show (f (Designator f)), Show (f (Statement f))) => Show (WithAlternative f)

deriving instance Data (Case Identity)
deriving instance Data (Case Ambiguous)
deriving instance (Show (f (Designator f)), Show (f (Statement f))) => Show (Case f)

deriving instance Data (CaseLabels Identity)
deriving instance Data (CaseLabels Ambiguous)
deriving instance Show (f (Designator f)) => Show (CaseLabels f)
