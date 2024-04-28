{-# LANGUAGE DeriveDataTypeable, KindSignatures, PolyKinds, RankNTypes, ScopedTypeVariables,
             TypeApplications, TypeFamilies, TypeFamilyDependencies, UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}

-- | Finally Tagless Abstract Syntax Tree definitions for the programming language Oberon

module Language.Oberon.Abstract (-- * Language classes
                                 Wirthy(..), CoWirthy(..), Oberon(..), Oberon2(..), Nameable(..),
                                 -- * Type synonyms
                                 Ident, IdentList, BaseType, ReturnType, ConstExpression,
                                 -- * Auxiliary data types
                                 RelOp(..), WirthySubsetOf(..), Maybe3(..),
                                 -- * Utilities
                                 just3, nothing3, maybe3, 
                                 ) where

import Data.Data (Data)
import qualified Data.Kind as K
import Data.List.NonEmpty
import Data.Text (Text)

import Prelude hiding (and, not, or, read, subtract)

type Ident = Text

-- | Relational operators
data RelOp = Equal | Unequal | Less | LessOrEqual | Greater | GreaterOrEqual | In
   deriving (Data, Eq, Show)

-- | The finally-tagless associated types and methods relevant to all programming languages designed by Niklaus
-- Wirth. Every non-leaf node type has four type variables:
--
-- * type variable @l@ represents the language of the constructs built by the methods,
-- * @l'@ is the language of the child node constructs,
-- * @f'@ wraps all descendant nodes, except
-- * @f@ wraps all direct children of the node.
class Wirthy l where
   type Module l      = (m :: K.Type -> (K.Type -> K.Type) -> (K.Type -> K.Type) -> K.Type) | m -> l
   type Declaration l = (d :: K.Type -> (K.Type -> K.Type) -> (K.Type -> K.Type) -> K.Type) | d -> l
   type Type l        = (t :: K.Type -> (K.Type -> K.Type) -> (K.Type -> K.Type) -> K.Type) | t -> l
   type Statement l   = (s :: K.Type -> (K.Type -> K.Type) -> (K.Type -> K.Type) -> K.Type) | s -> l
   type Expression l  = (e :: K.Type -> (K.Type -> K.Type) -> (K.Type -> K.Type) -> K.Type) | e -> l
   type Designator l  = (d :: K.Type -> (K.Type -> K.Type) -> (K.Type -> K.Type) -> K.Type) | d -> l
   type Value l       = (v :: K.Type -> (K.Type -> K.Type) -> (K.Type -> K.Type) -> K.Type) | v -> l

   type FieldList l         = (x :: K.Type -> (K.Type -> K.Type) -> (K.Type -> K.Type) -> K.Type) | x -> l
   type ProcedureHeading l  = (x :: K.Type -> (K.Type -> K.Type) -> (K.Type -> K.Type) -> K.Type) | x -> l
   type FormalParameters l  = (x :: K.Type -> (K.Type -> K.Type) -> (K.Type -> K.Type) -> K.Type) | x -> l
   type FPSection l         = (x :: K.Type -> (K.Type -> K.Type) -> (K.Type -> K.Type) -> K.Type) | x -> l
   type Block l             = (x :: K.Type -> (K.Type -> K.Type) -> (K.Type -> K.Type) -> K.Type) | x -> l
   type StatementSequence l = (x :: K.Type -> (K.Type -> K.Type) -> (K.Type -> K.Type) -> K.Type) | x -> l
   type Case l              = (x :: K.Type -> (K.Type -> K.Type) -> (K.Type -> K.Type) -> K.Type) | x -> l
   type CaseLabels l        = (x :: K.Type -> (K.Type -> K.Type) -> (K.Type -> K.Type) -> K.Type) | x -> l
   type ConditionalBranch l = (x :: K.Type -> (K.Type -> K.Type) -> (K.Type -> K.Type) -> K.Type) | x -> l
   type Element l           = (x :: K.Type -> (K.Type -> K.Type) -> (K.Type -> K.Type) -> K.Type) | x -> l
   
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

   -- Type
   pointerType :: f (Type l' l' f' f') -> Type l l' f' f
   procedureType :: Maybe (f (FormalParameters l' l' f' f')) -> Type l l' f' f
   typeReference :: QualIdent l' -> Type l l' f' f

   -- Statement
   assignment :: f (Designator l' l' f' f') -> f (Expression l' l' f' f') -> Statement l l' f' f
   caseStatement :: f (Expression l' l' f' f') -> [f (Case l' l' f' f')] -> Maybe (f (StatementSequence l' l' f' f')) 
                 -> Statement l l' f' f
   emptyStatement :: Statement l l' f' f
   exitStatement :: Statement l l' f' f
   ifStatement :: NonEmpty (f (ConditionalBranch l' l' f' f'))
               -> Maybe (f (StatementSequence l' l' f' f')) 
               -> Statement l l' f' f
   loopStatement :: f (StatementSequence l' l' f' f') -> Statement l l' f' f
   procedureCall :: f (Designator l' l' f' f') -> Maybe [f (Expression l' l' f' f')] -> Statement l l' f' f
   repeatStatement :: f (StatementSequence l' l' f' f') -> f (Expression l' l' f' f') -> Statement l l' f' f
   returnStatement :: Maybe (f (Expression l' l' f' f')) -> Statement l l' f' f
   whileStatement :: f (Expression l' l' f' f') -> f (StatementSequence l' l' f' f') -> Statement l l' f' f

   conditionalBranch :: f (Expression l' l' f' f') -> f (StatementSequence l' l' f' f') -> ConditionalBranch l l' f' f
   caseAlternative :: NonEmpty (f (CaseLabels l' l' f' f')) -> f (StatementSequence l' l' f' f') -> Case l l' f' f

   singleLabel :: f (ConstExpression l' l' f' f') -> CaseLabels l l' f' f
   labelRange :: f (ConstExpression l' l' f' f') -> f (ConstExpression l' l' f' f') -> CaseLabels l l' f' f

   statementSequence :: [f (Statement l' l' f' f')] -> StatementSequence l l' f' f

   -- Expression
   add, subtract :: f (Expression l' l' f' f') -> f (Expression l' l' f' f') -> Expression l l' f' f
   and, or :: f (Expression l' l' f' f') -> f (Expression l' l' f' f') -> Expression l l' f' f
   divide, integerDivide, modulo, multiply :: f (Expression l' l' f' f') -> f (Expression l' l' f' f') -> Expression l l' f' f
   functionCall :: f (Designator l' l' f' f') -> [f (Expression l' l' f' f')] -> Expression l l' f' f
   literal :: f (Value l' l' f' f') -> Expression l l' f' f
   negative, positive :: f (Expression l' l' f' f') -> Expression l l' f' f
   not :: f (Expression l' l' f' f') -> Expression l l' f' f
   read :: f (Designator l' l' f' f') -> Expression l l' f' f
   relation :: RelOp -> f (Expression l' l' f' f') -> f (Expression l' l' f' f') -> Expression l l' f' f

   element :: f (Expression l' l' f' f') -> Element l l' f' f
   range :: f (Expression l' l' f' f') -> f (Expression l' l' f' f') -> Element l l' f' f

   -- Value
   integer :: Integer -> Value l l' f' f
   nil, false, true :: Value l l' f' f
   real :: Double -> Value l l' f' f
   string :: Text -> Value l l' f' f
   charCode :: Int -> Value l l' f' f
   builtin :: Text -> Value l l' f' f

   -- Designator
   variable :: QualIdent l' -> Designator l l' f' f
   field :: f (Designator l' l' f' f') -> Ident -> Designator l l' f' f
   index :: f (Designator l' l' f' f') -> NonEmpty (f (Expression l' l' f' f')) -> Designator l l' f' f
   dereference :: f (Designator l' l' f' f') -> Designator l l' f' f

   -- Identifier
   identDef :: Ident -> IdentDef l
   nonQualIdent :: Ident -> QualIdent l

-- | An instance of this type can convert its own constructs to another language that's an instance of 'TargetClass'.
class Wirthy l => CoWirthy l where
   type TargetClass l :: K.Type -> K.Constraint
   type TargetClass l = Wirthy
   coDeclaration :: TargetClass l l' => Declaration l l'' f' f -> Declaration l' l'' f' f
   coType        :: TargetClass l l' => Type l l'' f' f        -> Type l' l'' f' f
   coStatement   :: TargetClass l l' => Statement l l'' f' f   -> Statement l' l'' f' f
   coExpression  :: TargetClass l l' => Expression l l'' f' f  -> Expression l' l'' f' f
   coDesignator  :: TargetClass l l' => Designator l l'' f' f  -> Designator l' l'' f' f
   coValue       :: TargetClass l l' => Value l l'' f' f       -> Value l' l'' f' f

-- | A language with constructs beyond the base 'Wirthy' class will have constructs that cannot be converted to a
-- | 'Wirthy' target. It can declare its 'TargetClass' to be this transformed language instead, whose language
-- | constructs are all wrapped in 'Maybe' or 'Maybe3'.
data WirthySubsetOf l = WirthySubsetOf l

-- | A modified 'Maybe' with kind that fits the types associated with 'Wirthy'.
newtype Maybe3 f a b c = Maybe3 (Maybe (f a b c)) deriving (Eq, Ord, Read, Show)

-- | Smart 'Maybe3' constructor corresponding to 'Just'
just3 = Maybe3 . Just
-- | Smart 'Maybe3' constructor corresponding to 'Nothing'
nothing3 = Maybe3 Nothing
-- | Smart 'Maybe3' destructor corresponding to 'maybe'
maybe3 n f (Maybe3 x) = maybe n f x

instance Wirthy l => Wirthy (WirthySubsetOf l) where
   type Module (WirthySubsetOf l)            = Maybe3 (Module l)
   type Declaration (WirthySubsetOf l)       = Maybe3 (Declaration l)
   type Type (WirthySubsetOf l)              = Maybe3 (Type l)
   type Statement (WirthySubsetOf l)         = Maybe3 (Statement l)
   type Expression (WirthySubsetOf l)        = Maybe3 (Expression l)
   type Designator (WirthySubsetOf l)        = Maybe3 (Designator l)
   type Value (WirthySubsetOf l)             = Maybe3 (Value l)

   type FieldList (WirthySubsetOf l)         = Maybe3 (FieldList l)
   type ProcedureHeading (WirthySubsetOf l)  = Maybe3 (ProcedureHeading l)
   type FormalParameters (WirthySubsetOf l)  = Maybe3 (FormalParameters l)
   type FPSection (WirthySubsetOf l)         = Maybe3 (FPSection l)
   type Block (WirthySubsetOf l)             = Maybe3 (Block l)
   type StatementSequence (WirthySubsetOf l) = Maybe3 (StatementSequence l)
   type Case (WirthySubsetOf l)              = Maybe3 (Case l)
   type CaseLabels (WirthySubsetOf l)        = Maybe3 (CaseLabels l)
   type ConditionalBranch (WirthySubsetOf l) = Maybe3 (ConditionalBranch l)
   type Element (WirthySubsetOf l)           = Maybe3 (Element l)
   
   type Import (WirthySubsetOf l)            = Maybe (Import l)
   type IdentDef (WirthySubsetOf l)          = Maybe (IdentDef l)
   type QualIdent (WirthySubsetOf l)         = Maybe (QualIdent l)

   -- Declaration
   constantDeclaration = (just3 .) . constantDeclaration @l
   typeDeclaration = (just3 .) . typeDeclaration @l
   variableDeclaration = (just3 .) . variableDeclaration @l
   procedureDeclaration = (just3 .) . procedureDeclaration @l

   formalParameters = (just3 .) . formalParameters @l
   fpSection = ((just3 .) .) . fpSection @l
   block = (just3 .) . block @l

   fieldList = (just3 .) . fieldList @l

   -- Type
   pointerType = just3 . pointerType @l
   procedureType = just3 . procedureType @l
   typeReference = just3 . typeReference @l

   -- Statement
   assignment = (just3 .) . assignment @l
   caseStatement = ((just3 .) .) . caseStatement @l
   emptyStatement = just3 (emptyStatement @l)
   exitStatement = just3 (exitStatement @l)
   ifStatement = (just3 .) . ifStatement @l
   loopStatement = just3 . loopStatement @l
   procedureCall = (just3 .) . procedureCall @l
   repeatStatement = (just3 .) . repeatStatement @l
   returnStatement = just3 . returnStatement @l
   whileStatement = (just3 .) . whileStatement @l

   conditionalBranch = (just3 .) . conditionalBranch @l
   caseAlternative = (just3 .) . caseAlternative @l

   singleLabel = just3 . singleLabel @l
   labelRange = (just3 .) . labelRange @l

   statementSequence = just3 . statementSequence @l

   -- Expression
   add = (just3 .) . add @l
   subtract = (just3 .) . subtract @l
   and = (just3 .) . and @l
   or = (just3 .) . or @l
   divide = (just3 .) . divide @l
   integerDivide = (just3 .) . integerDivide @l
   modulo = (just3 .) . modulo @l
   multiply = (just3 .) . multiply @l
   functionCall = (just3 .) . functionCall @l
   literal = just3 . literal @l
   negative = just3 . negative @l
   positive = just3 . positive @l
   not = just3 . not @l
   read = just3 . read @l
   relation = ((just3 .) .) . relation @l

   element = just3 . element @l
   range = (just3 .) . range @l

   -- Value
   integer = just3 . integer @l
   nil = just3 (nil @l)
   false = just3 (false @l)
   true = just3 (true @l)
   real = just3 . real @l
   string = just3 . string @l
   charCode = just3 . charCode @l
   builtin = just3 . builtin @l

   -- Designator
   variable = just3 . variable @l
   field = (just3 .) . field @l
   index = (just3 .) . index @l
   dereference = just3 . dereference @l

   -- Identifier
   identDef = Just . identDef @l
   nonQualIdent = Just . nonQualIdent @l

-- | Ability to deconstruct named constructs and obtain their 'Ident'.
class Wirthy l => Nameable l where
   getProcedureName :: Nameable l' => ProcedureHeading l l' f' f -> Ident
   getIdentDefName :: IdentDef l -> Ident
   getNonQualIdentName :: QualIdent l -> Maybe Ident

-- | The finally-tagless associated types and methods relevant to both versions of the Oberon language.
class Wirthy l => Oberon l where
   type WithAlternative l = (x :: K.Type -> (K.Type -> K.Type) -> (K.Type -> K.Type) -> K.Type) | x -> l

   moduleUnit :: Ident -> [Import l] -> f (Block l' l' f' f') -> Module l l' f' f
   moduleImport :: Maybe Ident -> Ident -> Import l
   qualIdent :: Ident -> Ident -> QualIdent l
   getQualIdentNames :: QualIdent l -> Maybe (Ident, Ident)
   exported :: Ident -> IdentDef l

   forwardDeclaration :: IdentDef l' -> Maybe (f (FormalParameters l' l' f' f')) -> Declaration l l' f' f
   procedureHeading :: Bool -> IdentDef l' -> Maybe (f (FormalParameters l' l' f' f')) -> ProcedureHeading l l' f' f

   arrayType :: [f (ConstExpression l' l' f' f')] -> f (Type l' l' f' f') -> Type l l' f' f
   recordType :: Maybe (BaseType l') -> [f (FieldList l' l' f' f')] -> Type l l' f' f

   withStatement :: f (WithAlternative l' l' f' f') -> Statement l l' f' f
   withAlternative :: QualIdent l' -> QualIdent l' -> f (StatementSequence l' l' f' f') -> WithAlternative l l' f' f

   is :: f (Expression l' l' f' f') -> QualIdent l' -> Expression l l' f' f
   set :: [f (Element l' l' f' f')] -> Expression l l' f' f

   typeGuard :: f (Designator l' l' f' f') -> QualIdent l' -> Designator l l' f' f

instance Wirthy l => Oberon (WirthySubsetOf l) where
   type WithAlternative (WirthySubsetOf l) = Maybe3 (WithAlternative l)
   moduleUnit = const $ const $ const nothing3
   moduleImport = const $ const Nothing
   qualIdent = const $ const Nothing
   getQualIdentNames = const Nothing
   exported = const Nothing

   forwardDeclaration = const $ const nothing3
   procedureHeading = const $ const $ const nothing3

   arrayType = const $ const nothing3
   recordType = const $ const nothing3

   withStatement = const nothing3
   withAlternative = const $ const $ const nothing3

   is = const $ const nothing3
   set = const nothing3

   typeGuard = const $ const nothing3

-- | The finally-tagless associated types and methods relevant to the Oberon 2 language.
class Oberon l => Oberon2 l where
   readOnly :: Ident -> IdentDef l
   typeBoundHeading :: Bool -> Ident -> Ident -> Bool -> IdentDef l' -> Maybe (f (FormalParameters l' l' f' f'))
                    -> ProcedureHeading l l' f' f
   forStatement :: Ident -> f (Expression l' l' f' f') -> f (Expression l' l' f' f')
                -> Maybe (f (Expression l' l' f' f'))
                -> f (StatementSequence l' l' f' f') 
                -> Statement l l' f' f
   variantWithStatement :: NonEmpty (f (WithAlternative l' l' f' f')) -> Maybe (f (StatementSequence l' l' f' f'))
                        -> Statement l l' f' f

instance Wirthy l => Oberon2 (WirthySubsetOf l) where
   readOnly = const Nothing
   typeBoundHeading = const $ const $ const $ const $ const $ const nothing3
   forStatement = const $ const $ const $ const $ const nothing3
   variantWithStatement = const $ const nothing3

type BaseType l = QualIdent l
type ReturnType l = QualIdent l
type ConstExpression l = Expression l
type IdentList l = NonEmpty (IdentDef l)
