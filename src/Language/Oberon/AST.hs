{-# LANGUAGE DeriveDataTypeable, FlexibleInstances, MultiParamTypeClasses, UndecidableInstances,
             StandaloneDeriving, TemplateHaskell #-}

-- | Oberon Abstract Syntax Tree definitions

module Language.Oberon.AST where

import Data.Data (Data, Typeable)
import Data.Functor.Identity (Identity)
import Data.List.NonEmpty
import Data.Text

import Rank2.Attributes (Transformation(remap), DeepTransformation(deepmap), Product)
import qualified Rank2.Attributes.TH

data Module f' f = Module Ident [Import] ([f (Declaration f' f')]) (Maybe (f (StatementSequence f' f'))) Ident

deriving instance (Typeable f, Typeable f',
                   Data (f (Declaration f' f')), Data (f (StatementSequence f' f'))) => Data (Module f' f)
deriving instance (Show (f (Declaration f' f')), Show (f (StatementSequence f' f'))) => Show (Module f' f)

type Ident = Text

type Import = (Maybe Ident, Ident)

data Declaration f' f = ConstantDeclaration IdentDef (f (ConstExpression f' f'))
                      | TypeDeclaration IdentDef (f (Type f' f'))
                      | VariableDeclaration IdentList (f (Type f' f'))
                      | ProcedureDeclaration (ProcedureHeading f' f) (ProcedureBody f' f) Ident
                      | ForwardDeclaration IdentDef (Maybe (f (FormalParameters f' f')))

deriving instance (Typeable f, Typeable f',
                   Data (f (Type f' f')), Data (f (ConstExpression f' f')), Data (f (FormalParameters f' f')),
                   Data (ProcedureHeading f' f), Data (ProcedureBody f' f)) => Data (Declaration f' f)
deriving instance (Show (f (Type f' f')), Show (f (ConstExpression f' f')), Show (f (FormalParameters f' f')),
                   Show (ProcedureHeading f' f), Show (ProcedureBody f' f)) => Show (Declaration f' f)

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

data RelOp = Equal | Unequal | Less | LessOrEqual | Greater | GreaterOrEqual | In | Is
   deriving (Data, Show)

data Element f' f = Element (f (Expression f' f'))
                  | Range (f (Expression f' f')) (f (Expression f' f'))

deriving instance (Typeable f, Typeable f', Data (f (Expression f' f'))) => Data (Element f' f)
deriving instance Show (f (Expression f' f')) => Show (Element f' f)

data Designator f' f = Variable QualIdent
                     | Field (f (Designator f' f')) Ident 
                     | Index (f (Designator f' f')) (NonEmpty (f (Expression f' f')))
                     | TypeGuard (f (Designator f' f')) QualIdent 
                     | Dereference (f (Designator f' f'))

deriving instance (Typeable f, Typeable f', Data (f (Designator f' f')), Data (f (Expression f' f'))) =>
                  Data (Designator f' f)
deriving instance (Show (f (Designator f' f')), Show (f (Expression f' f'))) => Show (Designator f' f)

data Type f' f = TypeReference QualIdent 
               | ArrayType [f (ConstExpression f' f')] (f (Type f' f'))
               | RecordType (Maybe BaseType) (NonEmpty (f (FieldList f' f')))
               | PointerType (f (Type f' f'))
               | ProcedureType (Maybe (f (FormalParameters f' f')))

deriving instance (Typeable f, Typeable f', Data (f (Type f' f')), Data (f (ConstExpression f' f')),
                   Data (f (FormalParameters f' f')), Data (f (FieldList f' f'))) => Data (Type f' f)
deriving instance (Show (f (Type f' f')), Show (f (ConstExpression f' f')),
                   Show (f (FormalParameters f' f')), Show (f (FieldList f' f'))) => Show (Type f' f)

data QualIdent = QualIdent Ident Ident 
               | NonQualIdent Ident
   deriving (Data, Eq, Ord, Show)

type BaseType  = QualIdent

data FieldList f' f = FieldList IdentList (f (Type f' f'))
                    | EmptyFieldList

deriving instance (Typeable f, Typeable f', Data (f (Type f' f')), Data (f (Expression f' f'))) => Data (FieldList f' f)
deriving instance (Show (f (Type f' f')), Show (f (Expression f' f'))) => Show (FieldList f' f)

type IdentList = NonEmpty IdentDef

data ProcedureHeading f' f = 
   ProcedureHeading (Maybe (Bool, Ident, Ident)) Bool IdentDef (Maybe (f (FormalParameters f' f')))
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
