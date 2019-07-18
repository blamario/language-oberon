{-# LANGUAGE DeriveDataTypeable, KindSignatures, PolyKinds, RankNTypes, TypeFamilies, TypeFamilyDependencies #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}

-- | Oberon Finally Tagless Abstract Syntax Tree definitions

module Language.Oberon.Abstract where

import Data.Data (Data, Typeable)
import Data.List.NonEmpty
import Data.Text (Text)

import Transformation.Deep (Product)

type Ident = Text

data RelOp = Equal | Unequal | Less | LessOrEqual | Greater | GreaterOrEqual | In
   deriving (Data, Eq, Show)

class Wirthy l where
   type Module l      = (m :: * -> (* -> *) -> (* -> *) -> *) | m -> l
   type Declaration l = (d :: * -> (* -> *) -> (* -> *) -> *) | d -> l
   type Type l        = (t :: * -> (* -> *) -> (* -> *) -> *) | t -> l
   type Statement l   = (s :: * -> (* -> *) -> (* -> *) -> *) | s -> l
   type Expression l  = (e :: * -> (* -> *) -> (* -> *) -> *) | e -> l
   type Designator l  = (d :: * -> (* -> *) -> (* -> *) -> *) | d -> l

   type FieldList l         = (x :: * -> (* -> *) -> (* -> *) -> *) | x -> l
   type ProcedureHeading l  = (x :: * -> (* -> *) -> (* -> *) -> *) | x -> l
   type FormalParameters l  = (x :: * -> (* -> *) -> (* -> *) -> *) | x -> l
   type FPSection l         = (x :: * -> (* -> *) -> (* -> *) -> *) | x -> l
   type Block l             = (x :: * -> (* -> *) -> (* -> *) -> *) | x -> l
   type StatementSequence l = (x :: * -> (* -> *) -> (* -> *) -> *) | x -> l
   type Case l              = (x :: * -> (* -> *) -> (* -> *) -> *) | x -> l
   type CaseLabels l        = (x :: * -> (* -> *) -> (* -> *) -> *) | x -> l
   type Element l           = (x :: * -> (* -> *) -> (* -> *) -> *) | x -> l
   
   type Import l  = x | x -> l
   type IdentDef l  = x | x -> l
   type QualIdent l = x | x -> l

   -- Declaration
   constantDeclaration :: IdentDef l' -> f (ConstExpression l' l' f' f') -> Declaration l l' f' f
   typeDeclaration :: IdentDef l' -> f (Type l' l' f' f') -> Declaration l l' f' f
   variableDeclaration :: IdentList l' -> f (Type l' l' f' f') -> Declaration l l' f' f
   procedureDeclaration :: f (ProcedureHeading l' l' f' f') -> f (Block l' l' f' f') -> Declaration l l' f' f

   formalParameters :: [f (FPSection l' l' f' f')] -> Maybe (ReturnType l') -> FormalParameters l l' f' f
   fpSection :: Bool -> [Ident] -> f (Type l' l' f' f') -> FPSection l l' f' f
   block :: [f (Declaration l' l' f' f')] -> Maybe (f (StatementSequence l' l' f' f')) -> Block l l' f' f

   fieldList :: NonEmpty (IdentDef l') -> f (Type l' l' f' f') -> FieldList l l' f' f
   emptyFieldList :: FieldList l l' f' f

   -- Type
   pointerType :: f (Type l' l' f' f') -> Type l l' f' f
   procedureType :: Maybe (f (FormalParameters l' l' f' f')) -> Type l l' f' f
   typeReference :: QualIdent l' -> Type l l' f' f

   -- Statement
   assignment :: f (Designator l' l' f' f') -> f (Expression l' l' f' f') -> Statement l l' f' f
   caseStatement :: f (Expression l' l' f' f') -> NonEmpty (f (Case l' l' f' f')) -> Maybe (f (StatementSequence l' l' f' f')) 
                 -> Statement l l' f' f
   emptyStatement :: Statement l l' f' f
   exitStatement :: Statement l l' f' f
   ifStatement :: NonEmpty (f (Product (Expression l' l') (StatementSequence l' l') f' f')) 
               -> Maybe (f (StatementSequence l' l' f' f')) 
               -> Statement l l' f' f
   loopStatement :: f (StatementSequence l' l' f' f') -> Statement l l' f' f
   procedureCall :: f (Designator l' l' f' f') -> Maybe [f (Expression l' l' f' f')] -> Statement l l' f' f
   repeatStatement :: f (StatementSequence l' l' f' f') -> f (Expression l' l' f' f') -> Statement l l' f' f
   returnStatement :: Maybe (f (Expression l' l' f' f')) -> Statement l l' f' f
   whileStatement :: f (Expression l' l' f' f') -> f (StatementSequence l' l' f' f') -> Statement l l' f' f

   caseAlternative :: NonEmpty (f (CaseLabels l' l' f' f')) -> f (StatementSequence l' l' f' f') -> Case l l' f' f
   emptyCase :: Case l l' f' f

   singleLabel :: f (ConstExpression l' l' f' f') -> CaseLabels l l' f' f
   labelRange :: f (ConstExpression l' l' f' f') -> f (ConstExpression l' l' f' f') -> CaseLabels l l' f' f

   statementSequence :: NonEmpty (f (Statement l' l' f' f')) -> StatementSequence l l' f' f

   -- Expression
   add, subtract :: f (Expression l' l' f' f') -> f (Expression l' l' f' f') -> Expression l l' f' f
   and, or :: f (Expression l' l' f' f') -> f (Expression l' l' f' f') -> Expression l l' f' f
   divide, integerDivide, modulo, multiply :: f (Expression l' l' f' f') -> f (Expression l' l' f' f') -> Expression l l' f' f
   functionCall :: f (Designator l' l' f' f') -> [f (Expression l' l' f' f')] -> Expression l l' f' f
   integer :: Integer -> Expression l l' f' f
   negative, positive :: f (Expression l' l' f' f') -> Expression l l' f' f
   nil, false, true :: Wirthy l' => (forall a. a -> f a) -> Expression l l' f' f
   not :: f (Expression l' l' f' f') -> Expression l l' f' f
   read :: f (Designator l' l' f' f') -> Expression l l' f' f
   real :: Double -> Expression l l' f' f
   relation :: RelOp -> f (Expression l' l' f' f') -> f (Expression l' l' f' f') -> Expression l l' f' f
   string :: Text -> Expression l l' f' f
   charCode :: Int -> Expression l l' f' f

   element :: f (Expression l' l' f' f') -> Element l l' f' f
   range :: f (Expression l' l' f' f') -> f (Expression l' l' f' f') -> Element l l' f' f

   -- Designator
   variable :: QualIdent l' -> Designator l l' f' f
   field :: f (Designator l' l' f' f') -> Ident -> Designator l l' f' f
   index :: f (Designator l' l' f' f') -> NonEmpty (f (Expression l' l' f' f')) -> Designator l l' f' f
   dereference :: f (Designator l' l' f' f') -> Designator l l' f' f

   -- Identifier
   identDef :: Ident -> IdentDef l
   nonQualIdent :: Ident -> QualIdent l

class CoWirthy l where
   coDeclaration :: (Wirthy (l' :: *), Traversable f, Traversable f') => Declaration l l'' f' f -> Maybe (Declaration l' l'' f' f)
   coType        :: (Wirthy (l' :: *), Traversable f, Traversable f') => Type l l'' f' f        -> Maybe (Type l' l'' f' f)
   coStatement   :: (Wirthy (l' :: *), Traversable f, Traversable f') => Statement l l'' f' f   -> Maybe (Statement l' l'' f' f)
   coExpression  :: (Wirthy (l' :: *), Wirthy (l'' :: *), Traversable f, Traversable f')
                 => (forall a. a -> f a) -> Expression l l'' f' f  -> Maybe (Expression l' l'' f' f)
   coDesignator  :: (Wirthy (l' :: *), Traversable f, Traversable f') => Designator l l'' f' f  -> Maybe (Designator l' l'' f' f)

class Wirthy l => Nameable l where
   getProcedureName :: Nameable l' => ProcedureHeading l l' f' f -> Ident
   getIdentDefName :: IdentDef l -> Ident
   getNonQualIdentName :: QualIdent l -> Maybe Ident
   toBool :: (Traversable f, Traversable f', CoWirthy l', Nameable l') => Expression l l' f' f -> Maybe Bool

class Wirthy l => Oberon l where
   type WithAlternative l = (x :: * -> (* -> *) -> (* -> *) -> *) | x -> l

   moduleUnit :: Ident -> [Import l] -> [f (Declaration l' l' f' f')] -> Maybe (f (StatementSequence l' l' f' f'))
              -> Module l l' f' f
   moduleImport :: Maybe Ident -> Ident -> Import l
   qualIdent :: Ident -> Ident -> QualIdent l
   getQualIdentNames :: QualIdent l -> Maybe (Ident, Ident)
   exported :: Ident -> IdentDef l

   forwardDeclaration :: IdentDef l' -> Maybe (f (FormalParameters l' l' f' f')) -> Declaration l l' f' f
   procedureHeading :: Bool -> IdentDef l' -> Maybe (f (FormalParameters l' l' f' f')) -> ProcedureHeading l l' f' f

   arrayType :: [f (ConstExpression l' l' f' f')] -> f (Type l' l' f' f') -> Type l l' f' f
   recordType :: Maybe (BaseType l') -> NonEmpty (f (FieldList l' l' f' f')) -> Type l l' f' f

   withStatement :: f (WithAlternative l' l' f' f') -> Statement l l' f' f
   withAlternative :: QualIdent l' -> QualIdent l' -> f (StatementSequence l' l' f' f') -> WithAlternative l l' f' f

   is :: f (Expression l' l' f' f') -> QualIdent l' -> Expression l l' f' f
   set :: [f (Element l' l' f' f')] -> Expression l l' f' f

   typeGuard :: f (Designator l' l' f' f') -> QualIdent l' -> Designator l l' f' f

class Oberon l => Oberon2 l where
   readOnly :: Ident -> IdentDef l
   typeBoundHeading :: Bool -> Ident -> Ident -> Bool -> IdentDef l' -> Maybe (f (FormalParameters l' l' f' f'))
                    -> ProcedureHeading l l' f' f
   forStatement :: Ident -> f (Expression l' l' f' f') -> f (Expression l' l' f' f') -> Maybe (f (Expression l' l' f' f'))
                -> f (StatementSequence l' l' f' f') 
                -> Statement l l' f' f
   variantWithStatement :: NonEmpty (f (WithAlternative l' l' f' f')) -> Maybe (f (StatementSequence l' l' f' f'))
                        -> Statement l l' f' f

type BaseType l = QualIdent l
type ReturnType l = QualIdent l
type ConstExpression l = Expression l
type IdentList l = NonEmpty (IdentDef l)
