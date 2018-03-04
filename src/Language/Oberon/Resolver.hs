module Language.Oberon.Resolver where

import Control.Applicative (Alternative)
import Control.Monad ((>=>))
import Data.Either (partitionEithers)
import Data.Either.Validation (Validation(..), validationToEither)
import Data.Functor.Identity (Identity(..))
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty
import Data.Monoid (Alt(..))
import Data.Map.Lazy (Map, traverseWithKey)
import qualified Data.Map.Lazy as Map
import Data.Semigroup (Semigroup(..), sconcat)

import Text.Grampa (Ambiguous(..))

import Language.Oberon.AST

data DeclarationRHS = DeclaredConstant (ConstExpression Identity)
                    | DeclaredType (Type Identity)
                    | DeclaredVariable (Type Identity)
                    | DeclaredProcedure (Maybe FormalParameters)
                    | DeclaredForward (Maybe FormalParameters)
   
data Error = UnknownModule Ident
           | UnknownLocal Ident
           | UnknownImport QualIdent
           | AmbiguousStatement [Statement Identity]
           | InvalidStatement (NonEmpty Error)
           | AmbiguousDesignator [Designator Identity]
           | InvalidDesignator (NonEmpty Error)

resolveModules :: Map Ident (Module Ambiguous) 
                       -> Validation (NonEmpty (Ident, NonEmpty Error)) (Map Ident (Module Identity))
resolveModules modules = traverseWithKey extractErrors modules'
   where modules' = resolveModule modules' <$> modules
         extractErrors moduleKey (Failure e)   = Failure ((moduleKey, e) :| [])
         extractErrors _         (Success mod) = Success mod

resolveModule :: Map Ident (Validation (NonEmpty Error) (Module Identity)) -> Module Ambiguous -> Validation (NonEmpty Error) (Module Identity)
resolveModule modules (Module name imports declarations body name') = module'
   where moduleExports      :: Map Ident (Map Ident DeclarationRHS)
         moduleGlobals      :: Map Ident (Bool, DeclarationRHS)
         resolveDeclaration :: Declaration Ambiguous -> Validation (NonEmpty Error) (Declaration Identity)
         resolveStatements  :: StatementSequence Ambiguous -> Validation (NonEmpty Error) (StatementSequence Identity)
         resolveStatement   :: Statement Ambiguous -> Validation (NonEmpty Error) (Statement Identity)
         resolveExpression  :: Expression Ambiguous -> Validation (NonEmpty Error) (Expression Identity)
         resolveDesignator  :: Designator Ambiguous -> Validation (NonEmpty Error) (Designator Identity)
         validateVariable   :: Designator Identity -> Validation (NonEmpty Error) (Designator Identity)

         module' = Module name imports 
                   <$> traverse resolveDeclaration declarations 
                   <*> traverse resolveStatements body 
                   <*> pure name'

         moduleExports = foldMap exportsOfModule <$> modules
         moduleGlobals = foldMap globalsOfModule module'

         resolveDeclaration = undefined

         resolveStatements =  traverse (fmap Identity . resolveOne)
            where resolveOne :: Ambiguous (Statement Ambiguous) -> Validation (NonEmpty Error) (Statement Identity)
                  resolveOne (Ambiguous statements) = uniqueStatement (resolveStatement <$> statements)

         resolveStatement EmptyStatement = pure EmptyStatement
         resolveStatement (Assignment (Ambiguous designators) exp) =
            Assignment <$> (Identity <$> uniqueDesignator ((resolveDesignator >=> validateVariable) <$> designators))
                       <*> resolveExpression exp
         resolveStatement (ProcedureCall (Ambiguous designators) Nothing) = undefined

         resolveExpression = undefined
         resolveDesignator = undefined
         
         validateVariable d@(Variable q@(QualIdent moduleName name)) =
            case Map.lookup moduleName moduleExports
            of Nothing -> Failure (UnknownModule moduleName :| [])
               Just exports -> case Map.lookup name exports
                               of Nothing -> Failure (UnknownImport q :| [])
                                  Just (DeclaredVariable t) -> Success d

exportsOfModule :: Module Identity -> Map Ident DeclarationRHS
exportsOfModule = Map.mapMaybe isExported . globalsOfModule
   where isExported (True, binding) = Just binding
         isExported (False, _) = Nothing

globalsOfModule :: Module Identity -> Map Ident (Bool, DeclarationRHS)
globalsOfModule (Module _ imports declarations _ _) = undefined

uniqueDesignator = unique InvalidDesignator AmbiguousDesignator
uniqueStatement = unique InvalidStatement AmbiguousStatement

unique :: (NonEmpty Error -> Error) -> ([a] -> Error) 
          -> NonEmpty (Validation (NonEmpty Error) a) -> Validation (NonEmpty Error) a
unique _ _ (x :| []) = x
unique inv amb xs = case partitionEithers (validationToEither <$> NonEmpty.toList xs)
                     of (_, [x]) -> Success x
                        (errors, []) -> Failure (inv (sconcat $ NonEmpty.fromList errors) :| [])
                        (_, stats) -> Failure (amb stats :| [])

instance Semigroup e => Monad (Validation e) where
   return = pure
   Failure e >>= _ = Failure e
   Success a >>= f = f a
