{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, UndecidableInstances, StandaloneDeriving #-}

-- | Oberon Abstract Syntax Tree definitions

module Language.Oberon.AST where

import Data.Data (Data, Typeable)
import Data.Functor.Identity (Identity)
import Data.List.NonEmpty
import Data.Text
import Text.Grampa (Ambiguous)

data Module f = Module Ident [Import] [Declaration f] (Maybe (StatementSequence f)) Ident

deriving instance (Typeable f, Data (f (Designator f)), Data (f (Expression f)), Data (f (Statement f))) =>
                  Data (Module f)
deriving instance (Show (f (Designator f)), Show (f (Expression f)), Show (f (Statement f))) => Show (Module f)

type Ident = Text

type Import = (Maybe Ident, Ident)

data Declaration f  = ConstantDeclaration IdentDef (f (ConstExpression f))
                    | TypeDeclaration IdentDef (Type f)
                    | VariableDeclaration IdentList (Type f)
                    | ProcedureDeclaration (ProcedureHeading f) (ProcedureBody f) Ident
                    | ForwardDeclaration IdentDef (Maybe (FormalParameters f))

deriving instance (Typeable f, Data (f (Designator f)), Data (f (Expression f)), Data (f (Statement f))) =>
                  Data (Declaration f)
deriving instance (Show (f (Designator f)), Show (f (Expression f)), Show (f (Statement f))) => Show (Declaration f)

data IdentDef = IdentDef Ident AccessMode
   deriving (Data, Eq, Ord, Show)

data AccessMode = Exported | ReadOnly | PrivateOnly
   deriving (Data, Eq, Ord, Show)

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

deriving instance (Typeable f, Data (f (Designator f))) => Data (Expression f)
deriving instance Show (f (Designator f)) => Show (Expression f)

data RelOp = Equal | Unequal | Less | LessOrEqual | Greater | GreaterOrEqual | In | Is
   deriving (Data, Show)

data Element f = Element (Expression f)
               | Range (Expression f) (Expression f)

deriving instance (Typeable f, Data (f (Designator f))) => Data (Element f)
deriving instance Show (f (Designator f)) => Show (Element f)

type AmbDesignator f = f (Designator f)

data Designator f = Variable QualIdent
                  | Field (Designator f) Ident 
                  | Index (Designator f) (NonEmpty (Expression f))
                  | TypeGuard (Designator f) QualIdent 
                  | Dereference (Designator f)

deriving instance (Typeable f, Data (f (Designator f))) => Data (Designator f)
deriving instance Show (f (Designator f)) => Show (Designator f)

type ActualParameters f = [Expression f]

data Type f = TypeReference QualIdent 
            | ArrayType [f (ConstExpression f)] (Type f)
            | RecordType (Maybe BaseType) (FieldListSequence f)
            | PointerType (Type f)
            | ProcedureType (Maybe (FormalParameters f))

deriving instance (Typeable f, Data (f (Designator f)), Data (f (Expression f))) => Data (Type f)
deriving instance (Show (f (Designator f)), Show (f (Expression f))) => Show (Type f)

data QualIdent = QualIdent Ident Ident 
               | NonQualIdent Ident
   deriving (Data, Eq, Ord, Show)

type BaseType  =  QualIdent

type FieldListSequence f = NonEmpty (FieldList f)

data FieldList f = FieldList IdentList (Type f)
                 | EmptyFieldList

deriving instance (Typeable f, Data (f (Designator f)), Data (f (Expression f))) => Data (FieldList f)
deriving instance (Show (f (Designator f)), Show (f (Expression f))) => Show (FieldList f)

type IdentList = NonEmpty IdentDef

data ProcedureHeading f =  ProcedureHeading (Maybe (Bool, Ident, Ident)) Bool IdentDef (Maybe (FormalParameters f))
data FormalParameters f  = FormalParameters [FPSection f] (Maybe QualIdent)
data FPSection f  =  FPSection Bool (NonEmpty Ident) (Type f)

deriving instance (Typeable f, Data (f (Designator f)),  Data (f (Expression f))) => Data (ProcedureHeading f)
deriving instance (Show (f (Designator f)),  Show (f (Expression f))) => Show (ProcedureHeading f)

deriving instance (Typeable f, Data (f (Designator f)),  Data (f (Expression f))) => Data (FormalParameters f)
deriving instance (Show (f (Designator f)),  Show (f (Expression f))) => Show (FormalParameters f)

deriving instance (Typeable f, Data (f (Designator f)),  Data (f (Expression f))) => Data (FPSection f)
deriving instance (Show (f (Designator f)),  Show (f (Expression f))) => Show (FPSection f)

data ProcedureBody f =  ProcedureBody [Declaration f] (Maybe (StatementSequence f))

deriving instance (Typeable f, Data (f (Designator f)), Data (f (Expression f)), Data (f (Statement f))) =>
                  Data (ProcedureBody f)
deriving instance (Show (f (Designator f)), Show (f (Expression f)), Show (f (Statement f))) => Show (ProcedureBody f)

type StatementSequence f  = NonEmpty (f (Statement f))

data Statement f = EmptyStatement
                 | Assignment (AmbDesignator f) (Expression f)
                 | ProcedureCall (AmbDesignator f) (Maybe (ActualParameters f))
                 | If (NonEmpty (Expression f, StatementSequence f)) (Maybe (StatementSequence f))
                 | CaseStatement (Expression f) (NonEmpty (Case f)) (Maybe (StatementSequence f))
                 | While (Expression f) (StatementSequence f)
                 | Repeat (StatementSequence f) (Expression f)
                 | For Ident (Expression f) (Expression f) (Maybe (Expression f)) (StatementSequence f)  -- Oberon2
                 | Loop (StatementSequence f)
                 | With (NonEmpty (WithAlternative f)) (Maybe (StatementSequence f))
                 | Exit 
                 | Return (Maybe (Expression f))

deriving instance (Typeable f, Data (f (Designator f)), Data (f (Statement f))) => Data (Statement f)
deriving instance (Show (f (Designator f)), Show (f (Statement f))) => Show (Statement f)

data WithAlternative f = WithAlternative QualIdent QualIdent (StatementSequence f)

data Case f = Case (NonEmpty (CaseLabels f)) (StatementSequence f)
            | EmptyCase

data CaseLabels f = SingleLabel (ConstExpression f)
                  | LabelRange (ConstExpression f) (ConstExpression f)

deriving instance (Typeable f, Data (f (Designator f)), Data (f (Statement f))) => Data (WithAlternative f)
deriving instance (Show (f (Designator f)), Show (f (Statement f))) => Show (WithAlternative f)

deriving instance (Typeable f, Data (f (Designator f)), Data (f (Statement f))) => Data (Case f)
deriving instance (Show (f (Designator f)), Show (f (Statement f))) => Show (Case f)

deriving instance (Typeable f, Data (f (Designator f))) => Data (CaseLabels f)
deriving instance Show (f (Designator f)) => Show (CaseLabels f)
