{-# LANGUAGE DeriveDataTypeable, KindSignatures, PolyKinds, TypeFamilies, TypeFamilyDependencies #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}

-- | Oberon Finally Tagless Abstract Syntax Tree definitions

module Language.Oberon.Abstract where

import Data.Data (Data, Typeable)
import Data.List.NonEmpty
import Data.Text (Text)

import Transformation.Deep (Product)

type Ident = Text

type Import = (Maybe Ident, Ident)

data QualIdent = QualIdent Ident Ident 
               | NonQualIdent Ident
   deriving (Data, Eq, Ord, Show)

type BaseType  = QualIdent

data RelOp = Equal | Unequal | Less | LessOrEqual | Greater | GreaterOrEqual | In
   deriving (Data, Eq, Show)

class Wirthy l where
   type Module l      = (m :: (* -> *) -> (* -> *) -> *) | m -> l
   type Declaration l = (d :: (* -> *) -> (* -> *) -> *) | d -> l
   type Type l        = (t :: (* -> *) -> (* -> *) -> *) | t -> l
   type Statement l   = (s :: (* -> *) -> (* -> *) -> *) | s -> l
   type Expression l  = (e :: (* -> *) -> (* -> *) -> *) | e -> l
   type Designator l  = (d :: (* -> *) -> (* -> *) -> *) | d -> l

   type FieldList l         = (x :: (* -> *) -> (* -> *) -> *) | x -> l
   type ProcedureHeading l  = (x :: (* -> *) -> (* -> *) -> *) | x -> l
   type FormalParameters l  = (x :: (* -> *) -> (* -> *) -> *) | x -> l
   type FPSection l         = (x :: (* -> *) -> (* -> *) -> *) | x -> l
   type ProcedureBody l     = (x :: (* -> *) -> (* -> *) -> *) | x -> l
   type StatementSequence l = (x :: (* -> *) -> (* -> *) -> *) | x -> l
   type WithAlternative l   = (x :: (* -> *) -> (* -> *) -> *) | x -> l
   type Case l              = (x :: (* -> *) -> (* -> *) -> *) | x -> l
   type CaseLabels l        = (x :: (* -> *) -> (* -> *) -> *) | x -> l
   type Element l           = (x :: (* -> *) -> (* -> *) -> *) | x -> l
   
   type IdentDef l   = x | x -> l

   -- Module
   moduleUnit :: Ident -> [Import] -> [f (Declaration l f' f')] -> Maybe (f (StatementSequence l f' f')) -> Module l f' f

   -- Declaration
   constantDeclaration :: IdentDef l -> f (ConstExpression l f' f') -> Declaration l f' f
   typeDeclaration :: IdentDef l -> f (Type l f' f') -> Declaration l f' f
   variableDeclaration :: IdentList l -> f (Type l f' f') -> Declaration l f' f
   procedureDeclaration :: f (ProcedureHeading l f' f') -> f (ProcedureBody l f' f') -> Declaration l f' f
   forwardDeclaration :: IdentDef l -> Maybe (f (FormalParameters l f' f')) -> Declaration l f' f

   procedureHeading :: Bool -> IdentDef l -> Maybe (f (FormalParameters l f' f')) -> ProcedureHeading l f' f
   formalParameters :: [f (FPSection l f' f')] -> Maybe QualIdent -> FormalParameters l f' f
   fpSection :: Bool -> NonEmpty Ident -> f (Type l f' f') -> FPSection l f' f
   procedureBody :: [f (Declaration l f' f')] -> Maybe (f (StatementSequence l f' f')) -> ProcedureBody l f' f
   
   identDef :: Ident -> IdentDef l

   fieldList :: NonEmpty (IdentDef l) -> f (Type l f' f') -> FieldList l f' f
   emptyFieldList :: FieldList l f' f

   -- Type
   arrayType :: [f (ConstExpression l f' f')] -> f (Type l f' f') -> Type l f' f
   pointerType :: f (Type l f' f') -> Type l f' f
   procedureType :: Maybe (f (FormalParameters l f' f')) -> Type l f' f
   recordType :: Maybe BaseType -> NonEmpty (f (FieldList l f' f')) -> Type l f' f
   typeReference :: QualIdent -> Type l f' f

   -- Statement
   assignment :: f (Designator l f' f') -> f (Expression l f' f') -> Statement l f' f
   caseStatement :: f (Expression l f' f') -> NonEmpty (f (Case l f' f')) -> Maybe (f (StatementSequence l f' f')) 
                 -> Statement l f' f
   emptyStatement :: Statement l f' f
   exitStatement :: Statement l f' f
   ifStatement :: NonEmpty (f (Product (Expression l) (StatementSequence l) f' f')) 
               -> Maybe (f (StatementSequence l f' f')) 
               -> Statement l f' f
   loopStatement :: f (StatementSequence l f' f') -> Statement l f' f
   procedureCall :: f (Designator l f' f') -> Maybe [f (Expression l f' f')] -> Statement l f' f
   repeatStatement :: f (StatementSequence l f' f') -> f (Expression l f' f') -> Statement l f' f
   returnStatement :: Maybe (f (Expression l f' f')) -> Statement l f' f
   whileStatement :: f (Expression l f' f') -> f (StatementSequence l f' f') -> Statement l f' f
   withStatement :: f (WithAlternative l f' f') -> Statement l f' f

   withAlternative :: QualIdent -> QualIdent -> f (StatementSequence l f' f') -> WithAlternative l f' f
   caseAlternative :: NonEmpty (f (CaseLabels l f' f')) -> f (StatementSequence l f' f') -> Case l f' f
   emptyCase :: Case l f' f

   singleLabel :: f (ConstExpression l f' f') -> CaseLabels l f' f
   labelRange :: f (ConstExpression l f' f') -> f (ConstExpression l f' f') -> CaseLabels l f' f

   statementSequence :: NonEmpty (f (Statement l f' f')) -> StatementSequence l f' f

   -- Expression
   add, subtract :: f (Expression l f' f') -> f (Expression l f' f') -> Expression l f' f
   and, or :: f (Expression l f' f') -> f (Expression l f' f') -> Expression l f' f
   charCode :: Int -> Expression l f' f
   charConstant :: Char -> Expression l f' f
   divide, integerDivide, modulo, multiply :: f (Expression l f' f') -> f (Expression l f' f') -> Expression l f' f
   functionCall :: f (Designator l f' f') -> [f (Expression l f' f')] -> Expression l f' f
   integer :: Text -> Expression l f' f
   negative, positive :: f (Expression l f' f') -> Expression l f' f
   nil :: Expression l f' f
   not :: f (Expression l f' f') -> Expression l f' f
   read :: f (Designator l f' f') -> Expression l f' f
   real :: Text -> Expression l f' f
   relation :: RelOp -> f (Expression l f' f') -> f (Expression l f' f') -> Expression l f' f
   set :: [f (Element l f' f')] -> Expression l f' f
   string :: Text -> Expression l f' f

   element :: f (Expression l f' f') -> Element l f' f
   range :: f (Expression l f' f') -> f (Expression l f' f') -> Element l f' f

   -- Designator
   variable :: QualIdent -> Designator l f' f
   field :: f (Designator l f' f') -> Ident -> Designator l f' f
   index :: f (Designator l f' f') -> NonEmpty (f (Expression l f' f')) -> Designator l f' f
   typeGuard :: f (Designator l f' f') -> QualIdent -> Designator l f' f
   dereference :: f (Designator l f' f') -> Designator l f' f

class Wirthy l => Nameable l where
   getProcedureName :: ProcedureHeading l f' f -> Ident
   getIdentDefName :: IdentDef l -> Ident

class Wirthy l => Oberon l where
   is :: f (Expression l f' f') -> QualIdent -> Expression l f' f
   exported :: Ident -> IdentDef l

class Oberon l => Oberon2 l where
   readOnly :: Ident -> IdentDef l
   typeBoundHeading :: Bool -> Ident -> Ident -> Bool -> IdentDef l -> Maybe (f (FormalParameters l f' f'))
                    -> ProcedureHeading l f' f
   forStatement :: Ident -> f (Expression l f' f') -> f (Expression l f' f') -> Maybe (f (Expression l f' f')) 
                -> f (StatementSequence l f' f') 
                -> Statement l f' f
   variantWithStatement :: NonEmpty (f (WithAlternative l f' f')) -> Maybe (f (StatementSequence l f' f')) -> Statement l f' f

type ConstExpression l = Expression l
type IdentList l = NonEmpty (IdentDef l)
