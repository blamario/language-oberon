{-# LANGUAGE OverloadedStrings #-}

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
           | NotAVariable QualIdent

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
         resolveStatements  :: Map Ident DeclarationRHS -> StatementSequence Ambiguous
                            -> Validation (NonEmpty Error) (StatementSequence Identity)
         resolveStatement   :: Map Ident DeclarationRHS -> Statement Ambiguous
                            -> Validation (NonEmpty Error) (Statement Identity)
         resolveExpression  :: Map Ident DeclarationRHS -> Expression Ambiguous
                            -> Validation (NonEmpty Error) (Expression Identity)
         resolveDesignator  :: Map Ident DeclarationRHS -> Designator Ambiguous
                            -> Validation (NonEmpty Error) (Designator Identity)
         validateVariable   :: Map Ident DeclarationRHS -> Designator Identity
                            -> Validation (NonEmpty Error) (Designator Identity)

         module' = Module name imports 
                   <$> traverse resolveDeclaration declarations 
                   <*> traverse (resolveStatements moduleGlobalScope) body 
                   <*> pure name'

         moduleExports = foldMap exportsOfModule <$> modules
         moduleGlobals = foldMap globalsOfModule module'
         moduleGlobalScope = Map.union (snd <$> moduleGlobals) predefined

         resolveDeclaration = undefined

         resolveStatements scope = traverse (fmap Identity . resolveOne)
            where resolveOne :: Ambiguous (Statement Ambiguous) -> Validation (NonEmpty Error) (Statement Identity)
                  resolveOne (Ambiguous statements) = uniqueStatement (resolveStatement scope <$> statements)

         resolveStatement _ EmptyStatement = pure EmptyStatement
         resolveStatement scope (Assignment (Ambiguous designators) exp) =
            Assignment <$> (Identity <$> uniqueDesignator ((resolveDesignator scope >=> validateVariable scope)
                                                           <$> designators))
                       <*> resolveExpression scope exp
         resolveStatement scope (ProcedureCall (Ambiguous designators) Nothing) = undefined

         resolveExpression scope = undefined
         resolveDesignator scope = undefined
         
         validateVariable _ d@(Variable q@(QualIdent moduleName name)) =
            case Map.lookup moduleName moduleExports
            of Nothing -> Failure (UnknownModule moduleName :| [])
               Just exports -> case Map.lookup name exports
                               of Nothing -> Failure (UnknownImport q :| [])
                                  Just (DeclaredVariable t) -> Success d
                                  Just _ -> Failure (NotAVariable q :| [])
         validateVariable scope d@(Variable q@(NonQualIdent name)) =
            case Map.lookup name scope
            of Nothing -> Failure (UnknownImport q :| [])
               Just (DeclaredVariable t) -> Success d
               Just _ -> Failure (NotAVariable q :| [])

predefined :: Map Ident DeclarationRHS
predefined = Map.fromList
   [("BOOLEAN", DeclaredType (TypeReference $ NonQualIdent "BOOLEAN")),
    ("CHAR", DeclaredType (TypeReference $ NonQualIdent "CHAR")),
    ("SHORTINT", DeclaredType (TypeReference $ NonQualIdent "SHORTINT")),
    ("INTEGER", DeclaredType (TypeReference $ NonQualIdent "INTEGER")),
    ("LONGINT", DeclaredType (TypeReference $ NonQualIdent "LONGINT")),
    ("REAL", DeclaredType (TypeReference $ NonQualIdent "REAL")),
    ("LONGREAL", DeclaredType (TypeReference $ NonQualIdent "LONGREAL")),
    ("SET", DeclaredType (TypeReference $ NonQualIdent "SET")),
    ("TRUE", DeclaredConstant (Read $ Identity $ Variable $ NonQualIdent "TRUE")),
    ("FALSE", DeclaredConstant (Read $ Identity $ Variable $ NonQualIdent "FALSE")),
    ("ABS", DeclaredProcedure $ Just $
            FormalParameters [FPSection False (pure "n") $ FormalTypeReference $ NonQualIdent "INTEGER"] $
            Just $ NonQualIdent "INTEGER"),
    ("ASH", DeclaredProcedure $ Just $
            FormalParameters [FPSection False (pure "n") $ FormalTypeReference $ NonQualIdent "INTEGER"] $
            Just $ NonQualIdent "INTEGER"),
    ("CAP", DeclaredProcedure $ Just $
            FormalParameters [FPSection False (pure "c") $ FormalTypeReference $ NonQualIdent "INTEGER"] $
            Just $ NonQualIdent "CAP"),
    ("LEN", DeclaredProcedure $ Just $
            FormalParameters [FPSection False (pure "c") $ FormalTypeReference $ NonQualIdent "ARRAY"] $
            Just $ NonQualIdent "LONGINT"),
    ("MAX", DeclaredProcedure $ Just $
            FormalParameters [FPSection False (pure "c") $ FormalTypeReference $ NonQualIdent "SET"] $
            Just $ NonQualIdent "INTEGER"),
    ("MIN", DeclaredProcedure $ Just $
            FormalParameters [FPSection False (pure "c") $ FormalTypeReference $ NonQualIdent "SET"] $
            Just $ NonQualIdent "INTEGER"),
    ("ODD", DeclaredProcedure $ Just $
            FormalParameters [FPSection False (pure "n") $ FormalTypeReference $ NonQualIdent "CHAR"] $
            Just $ NonQualIdent "BOOLEAN"),
    ("SIZE", DeclaredProcedure $ Just $
             FormalParameters [FPSection False (pure "n") $ FormalTypeReference $ NonQualIdent "CHAR"] $
             Just $ NonQualIdent "INTEGER"),
    ("ORD", DeclaredProcedure $ Just $
            FormalParameters [FPSection False (pure "n") $ FormalTypeReference $ NonQualIdent "CHAR"] $
            Just $ NonQualIdent "INTEGER"),
    ("CHR", DeclaredProcedure $ Just $
            FormalParameters [FPSection False (pure "n") $ FormalTypeReference $ NonQualIdent "INTEGER"] $
            Just $ NonQualIdent "CHAR"),
    ("SHORT", DeclaredProcedure $ Just $
              FormalParameters [FPSection False (pure "n") $ FormalTypeReference $ NonQualIdent "INTEGER"] $
              Just $ NonQualIdent "INTEGER"),
    ("LONG", DeclaredProcedure $ Just $
             FormalParameters [FPSection False (pure "n") $ FormalTypeReference $ NonQualIdent "INTEGER"] $
             Just $ NonQualIdent "INTEGER"),
    ("ENTIER", DeclaredProcedure $ Just $
               FormalParameters [FPSection False (pure "n") $ FormalTypeReference $ NonQualIdent "REAL"] $
               Just $ NonQualIdent "INTEGER"),
    ("INC", DeclaredProcedure $ Just $
            FormalParameters [FPSection False (pure "n") $ FormalTypeReference $ NonQualIdent "INTEGER"] Nothing),
    ("DEC", DeclaredProcedure $ Just $
            FormalParameters [FPSection False (pure "n") $ FormalTypeReference $ NonQualIdent "INTEGER"] Nothing),
    ("INCL", DeclaredProcedure $ Just $
             FormalParameters [FPSection False (pure "s") $ FormalTypeReference $ NonQualIdent "SET",
                               FPSection False (pure "n") $ FormalTypeReference $ NonQualIdent "INTEGER"] Nothing),
    ("EXCL", DeclaredProcedure $ Just $
             FormalParameters [FPSection False (pure "s") $ FormalTypeReference $ NonQualIdent "SET",
                               FPSection False (pure "n") $ FormalTypeReference $ NonQualIdent "INTEGER"] Nothing),
    ("COPY", DeclaredProcedure $ Just $
             FormalParameters [FPSection False (pure "s") $ FormalTypeReference $ NonQualIdent "ARRAY",
                               FPSection False (pure "n") $ FormalTypeReference $ NonQualIdent "ARRAY"] Nothing),
    ("NEW", DeclaredProcedure $ Just $
            FormalParameters [FPSection False (pure "n") $ FormalTypeReference $ NonQualIdent "POINTER"] Nothing),
    ("HALT", DeclaredProcedure $ Just $
             FormalParameters [FPSection False (pure "n") $ FormalTypeReference $ NonQualIdent "INTEGER"] Nothing)]

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
