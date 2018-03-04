{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, UndecidableInstances, StandaloneDeriving #-}

module Language.Oberon.AST where

import Data.Data (Data)
import Data.Functor.Classes (Show1, showsPrec1)
import Data.Functor.Identity (Identity)
import Data.List.NonEmpty
import Data.Text
import Text.Grampa (Ambiguous)

data Module f = Module Ident [Import] [Declaration f] (Maybe (StatementSequence f)) Ident

deriving instance Data (Module Identity)
deriving instance Data (Module Ambiguous)
deriving instance (Show1 f, Show (f (Statement f))) => Show (Module f)

type Ident = Text

data Import = Import Ident (Maybe Ident)
   deriving (Data, Show)

data Declaration f  = ConstantDeclaration IdentDef (ConstExpression f)
                    | TypeDeclaration IdentDef (Type f)
                    | VariableDeclaration IdentList (Type f)
                    | ProcedureDeclaration ProcedureHeading (ProcedureBody f) Ident
                    | ForwardDeclaration Ident Bool (Maybe FormalParameters)

deriving instance Data (Declaration Identity)
deriving instance Data (Declaration Ambiguous)
deriving instance (Show1 f, Show (f (Statement f))) => Show (Declaration f)

data IdentDef = IdentDef Ident Bool
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
deriving instance Show1 f => Show (Expression f)

data RelOp = Equal | Unequal | Less | LessOrEqual | Greater | GreaterOrEqual | In | Is
   deriving (Data, Show)

data Element f = Element (Expression f)
               | Range (Expression f) (Expression f)

deriving instance Data (Element Identity)
deriving instance Data (Element Ambiguous)
deriving instance Show1 f => Show (Element f)
instance Show1 f => Show (f (Element f)) where
   showsPrec = showsPrec1

type AmbDesignator f = f (Designator f)

data Designator f = Variable QualIdent
                  | Field (Designator f) Ident 
                  | Index (Designator f) (NonEmpty (Expression f))
                  | TypeGuard (Designator f) QualIdent 
                  | Dereference (Designator f)

deriving instance Data (Designator Identity)
deriving instance Data (Designator Ambiguous)
deriving instance Show1 f => Show (Designator f)
instance Show1 f => Show (f (Designator f)) where
   showsPrec = showsPrec1

type ActualParameters f = [Expression f]

data Type f = TypeReference QualIdent 
            | ArrayType (NonEmpty (ConstExpression f)) (Type f)
            | RecordType (Maybe BaseType) (FieldListSequence f)
            | PointerType (Type f)
            | ProcedureType (Maybe FormalParameters)

deriving instance Data (Type Identity)
deriving instance Data (Type Ambiguous)
deriving instance Show1 f => Show (Type f)
instance Show1 f => Show (f (Type f)) where
   showsPrec = showsPrec1

data QualIdent = QualIdent Ident Ident 
               | NonQualIdent Ident
   deriving (Data, Show)

type BaseType  =  QualIdent

type FieldListSequence f = [FieldList f]

data FieldList f = FieldList IdentList (Type f)

deriving instance Data (FieldList Identity)
deriving instance Data (FieldList Ambiguous)
deriving instance Show1 f => Show (FieldList f)
instance Show1 f => Show (f (FieldList f)) where
   showsPrec = showsPrec1

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

data ProcedureBody f =  ProcedureBody [Declaration f] (Maybe (StatementSequence f))

deriving instance Data (ProcedureBody Identity)
deriving instance Data (ProcedureBody Ambiguous)
deriving instance (Show1 f, Show (f (Statement f))) => Show (ProcedureBody f)

type StatementSequence f  = [f (Statement f)]

data Statement f = EmptyStatement
                 | Assignment (AmbDesignator f) (Expression f)
                 | ProcedureCall (AmbDesignator f) (Maybe (ActualParameters f))
                 | If (Expression f) (StatementSequence f) [((Expression f), (StatementSequence f))] 
                      (Maybe (StatementSequence f))
                 | CaseStatement (Expression f) (NonEmpty (Maybe (Case f))) (Maybe (StatementSequence f))
                 | While (Expression f) (StatementSequence f)
                 | Repeat (StatementSequence f) (Expression f)
                 | For Ident (Expression f) (Expression f) (Maybe (Expression f)) (StatementSequence f)  -- Oberon2
                 | Loop (StatementSequence f)
                 | With QualIdent QualIdent (StatementSequence f)
                 | Exit 
                 | Return (Maybe (Expression f))

deriving instance Data (Statement Identity)
deriving instance Data (Statement Ambiguous)
deriving instance (Show1 f, Show (f (Statement f))) => Show (Statement f)

data Case f = Case (NonEmpty (CaseLabels f)) (StatementSequence f)

data CaseLabels f = SingleLabel (ConstExpression f)
                  | LabelRange (ConstExpression f) (ConstExpression f)

deriving instance Data (Case Identity)
deriving instance Data (Case Ambiguous)
deriving instance (Show1 f, Show (f (Statement f))) => Show (Case f)

deriving instance Data (CaseLabels Identity)
deriving instance Data (CaseLabels Ambiguous)
deriving instance Show1 f => Show (CaseLabels f)
