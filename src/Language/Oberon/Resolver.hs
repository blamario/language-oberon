{-# LANGUAGE FlexibleContexts, FlexibleInstances, KindSignatures, MultiParamTypeClasses, OverloadedStrings,
             ScopedTypeVariables, StandaloneDeriving, TemplateHaskell, TypeFamilies, UndecidableInstances #-}
{-# OPTIONS_GHC -Wno-simplifiable-class-constraints #-}

-- | This module exports functions for resolving the syntactic ambiguities in a parsed module. For example, an Oberon
-- expression @foo(bar)@ may be a call to function @foo@ with a parameter @bar@, or it may be type guard on variable
-- @foo@ casting it to type @bar@.

module Language.Oberon.Resolver (Error(..),
                                 Predefined, predefined, predefined2, resolveModule, resolveModules) where

import Control.Monad.Trans.State (StateT(..), evalStateT, execStateT, get, put)
import Data.Either (partitionEithers)
import Data.Either.Validation (Validation(..), validationToEither)
import Data.Foldable (toList)
import Data.Functor.Compose (Compose(..))
import Data.List.NonEmpty (NonEmpty(..))
import qualified Data.List.NonEmpty as NonEmpty
import qualified Data.List as List
import Data.Map.Lazy (Map, traverseWithKey)
import qualified Data.Map.Lazy as Map
import Data.Semigroup (Semigroup(..), sconcat)
import Data.Text (Text)

import qualified Rank2.TH
import qualified Transformation as Shallow
import qualified Transformation.Deep as Deep
import qualified Transformation.Deep.TH
import qualified Transformation.Full as Full
import Text.Grampa (Ambiguous(..))

import qualified Language.Oberon.Abstract as Abstract
import Language.Oberon.AST

data DeclarationRHS l f' f = DeclaredConstant (f (Abstract.ConstExpression l l f' f'))
                           | DeclaredType (f (Abstract.Type l l f' f'))
                           | DeclaredVariable (f (Abstract.Type l l f' f'))
                           | DeclaredProcedure Bool (Maybe (f (Abstract.FormalParameters l l f' f')))
deriving instance (Show (Abstract.FormalParameters l l Placed Placed), Show (Abstract.Type l l Placed Placed),
                   Show (Abstract.ConstExpression l l Placed Placed)) =>
                  Show (DeclarationRHS l Placed Placed)
deriving instance (Show (Abstract.FormalParameters l l NodeWrap NodeWrap), Show (Abstract.Type l l NodeWrap NodeWrap),
                   Show (Abstract.ConstExpression l l NodeWrap NodeWrap)) =>
                  Show (DeclarationRHS l NodeWrap NodeWrap)

-- | All possible resolution errors
data Error l = UnknownModule (Abstract.QualIdent l)
             | UnknownLocal Ident
             | UnknownImport (Abstract.QualIdent l)
             | AmbiguousParses
             | AmbiguousDeclaration [Declaration l l NodeWrap NodeWrap]
             | AmbiguousDesignator [Designator l l NodeWrap NodeWrap]
             | AmbiguousExpression [Expression l l NodeWrap NodeWrap]
             | AmbiguousRecord [Designator l l NodeWrap NodeWrap]
             | AmbiguousStatement [Statement l l NodeWrap NodeWrap]
             | InvalidExpression (NonEmpty (Error l))
             | InvalidFunctionParameters [NodeWrap (Abstract.Expression l l NodeWrap NodeWrap)]
             | InvalidRecord (NonEmpty (Error l))
             | InvalidStatement (NonEmpty (Error l))
             | NotARecord (Abstract.QualIdent l)
             | NotAType (Abstract.QualIdent l)
             | NotAValue (Abstract.QualIdent l)
             | ClashingImports
             | UnparseableModule Text
deriving instance (Show (Abstract.QualIdent l),
                   Show (Declaration l l NodeWrap NodeWrap), Show (Statement l l NodeWrap NodeWrap),
                   Show (Expression l l NodeWrap NodeWrap), Show (Abstract.Expression l l NodeWrap NodeWrap),
                   Show (Designator l l NodeWrap NodeWrap)) => Show (Error l)

type Placed = ((,) Int)
type NodeWrap = Compose Placed Ambiguous

type Scope l = Map Ident (Validation (NonEmpty (Error l)) (DeclarationRHS l Placed Placed))

-- | A set of predefined declarations.
type Predefined l = Scope l

data Resolution l = Resolution{_modules :: Map Ident (Scope l)}

type Resolved l = StateT (Scope l, ResolutionState) (Validation (NonEmpty (Error l)))

data ResolutionState = ModuleState
                     | DeclarationState
                     | StatementState
                     | ExpressionState
                     | ExpressionOrTypeState
                     deriving (Eq, Show)

instance Monad (Validation (NonEmpty (Error l))) where
   Success s >>= f = f s
   Failure errors >>= _ = Failure errors

instance Shallow.Functor (Resolution l) NodeWrap (Resolved l) (Module l l (Resolved l) (Resolved l)) where
   (<$>) = mapResolveDefault

instance {-# overlappable #-} --Show (g Placed Placed) =>
                              Shallow.Traversable (Resolution l) NodeWrap Placed (Resolved l) (g Placed Placed) where
   traverse = traverseResolveDefault

instance {-# overlappable #-} --Show (g NodeWrap NodeWrap) =>
                              Shallow.Traversable (Resolution l) NodeWrap Placed (Resolved l) (g NodeWrap NodeWrap) where
   traverse = traverseResolveDefault

instance {-# overlaps #-}
   Resolvable l =>
   Shallow.Traversable (Resolution l) NodeWrap Placed (Resolved l) (Designator l l NodeWrap NodeWrap) where
   traverse res (Compose (pos, Ambiguous designators)) = StateT $ \s@(scope, state)->
      case partitionEithers (NonEmpty.toList (validationToEither . resolveDesignator res scope state <$> designators))
      of (_, [x]) -> Success ((pos, x), s)
         (errors, []) -> Failure (sconcat $ NonEmpty.fromList errors)
         (_, multi) -> Failure (AmbiguousDesignator multi :| [])

class Readable l where
   getVariableName :: Abstract.Designator l l f' f -> Maybe (Abstract.QualIdent l)

instance Readable Language where
   getVariableName (Variable q) = Just q
   getVariableName _ = Nothing

instance {-# overlaps #-}
   (Readable l, Abstract.Nameable l, Abstract.Oberon l,
    Deep.Traversable (Resolution l) (Abstract.Expression l l) NodeWrap Placed (Resolved l),
    Deep.Traversable (Resolution l) (Abstract.Designator l l) NodeWrap Placed (Resolved l),
    Shallow.Traversable (Resolution l) NodeWrap Placed (Resolved l) (Abstract.Expression l l NodeWrap NodeWrap),
    Shallow.Traversable (Resolution l) NodeWrap Placed (Resolved l) (Abstract.Designator l l NodeWrap NodeWrap)) =>
   Shallow.Traversable (Resolution l) NodeWrap Placed (Resolved l) (Expression l l NodeWrap NodeWrap) where
   traverse res expressions = StateT $ \s@(scope, state)->
      let resolveExpression :: Expression l l NodeWrap NodeWrap
                            -> Validation (NonEmpty (Error l)) (Expression l l NodeWrap NodeWrap, ResolutionState)
          resolveExpression e@(Read designators) =
             case evalStateT (Shallow.traverse res designators) s
             of Failure errors -> Failure errors
                Success{} -> pure (e, state)
          resolveExpression e@(FunctionCall functions parameters) =
             case evalStateT (Shallow.traverse res functions) s
             of Failure errors -> Failure errors
                Success (_pos, d)
                   | Just q <- getVariableName d, Success (DeclaredProcedure True _) <- resolveName res scope q
                     -> pure (e, ExpressionOrTypeState)
                   | Success{} <- evalStateT (traverse (Shallow.traverse res) parameters) (scope, ExpressionState)
                     -> pure (e, ExpressionState)
                   | otherwise -> Failure (pure $ InvalidFunctionParameters parameters)
          resolveExpression e@(IsA _lefts q) =
            case resolveName res scope q
            of Failure err ->  Failure err
               Success DeclaredType{} -> pure (e, ExpressionState)
               Success _ -> Failure (NotAType q :| [])
          resolveExpression e = pure (e, state)
      in (\(pos, (r, s'))-> ((pos, r), (scope, s')))
         <$> unique InvalidExpression (AmbiguousExpression . (fst <$>)) (resolveExpression <$> expressions)

instance {-# overlaps #-}
   (BindableDeclaration l, CoFormalParameters l, Abstract.Wirthy l,
    Full.Traversable (Resolution l) (Abstract.Type l l) NodeWrap Placed (Resolved l),
    Full.Traversable (Resolution l) (Abstract.FormalParameters l l) NodeWrap Placed (Resolved l),
    Full.Traversable (Resolution l) (Abstract.ConstExpression l l) NodeWrap Placed (Resolved l),
    Deep.Traversable (Resolution l) (Abstract.Type l l) NodeWrap Placed (Resolved l),
    Deep.Traversable (Resolution l) (Abstract.ProcedureHeading l l) NodeWrap Placed (Resolved l),
    Deep.Traversable (Resolution l) (Abstract.FormalParameters l l) NodeWrap Placed (Resolved l),
    Deep.Traversable (Resolution l) (Abstract.ConstExpression l l) NodeWrap Placed (Resolved l),
    Shallow.Traversable (Resolution l) NodeWrap Placed (Resolved l)
                        (Abstract.ProcedureHeading l l NodeWrap NodeWrap),
    Shallow.Traversable (Resolution l) NodeWrap Placed (Resolved l)
                        (Abstract.Block l l NodeWrap NodeWrap)) =>
   Shallow.Traversable (Resolution l) NodeWrap Placed (Resolved l) (Declaration l l NodeWrap NodeWrap) where
   traverse res (Compose (pos, Ambiguous (proc@(ProcedureDeclaration heading body) :| []))) =
      do s@(scope, state) <- get
         let Success (headingScope, _) = execStateT (Shallow.traverse res heading) s
             Success (_, body') = evalStateT (Shallow.traverse res body) s
             innerScope = localScope res "" (getLocalDeclarations body') (headingScope `Map.union` scope)
         put (innerScope, state)
         return (pos, proc)
   traverse _ (Compose (pos, Ambiguous (dec :| []))) = pure (pos, dec)
   traverse _ declarations = StateT (const $ Failure $ pure $ AmbiguousDeclaration $ toList declarations)

class CoFormalParameters l where
   getFPSections :: Abstract.FormalParameters l l f' f -> [f (Abstract.FPSection l l f' f')]
   evalFPSection :: Abstract.FPSection l l f' f -> (Bool -> [Ident] -> f (Abstract.Type l l f' f') -> r) -> r
   getLocalDeclarations :: Abstract.Block l l f' f -> [f (Abstract.Declaration l l f' f')]

instance CoFormalParameters Language where
   getFPSections (FormalParameters sections _) = sections
   evalFPSection (FPSection var names types) f = f var names types
   getLocalDeclarations (Block declarations _statements) = declarations

instance {-# overlaps #-}
   (Abstract.Wirthy l, CoFormalParameters l,
    Full.Traversable (Resolution l) (Abstract.Type l l) NodeWrap Placed (Resolved l),
    Full.Traversable (Resolution l) (Abstract.FormalParameters l l) NodeWrap Placed (Resolved l),
    Full.Traversable (Resolution l) (Abstract.ConstExpression l l) NodeWrap Placed (Resolved l),
    Deep.Traversable (Resolution l) (Abstract.Type l l) NodeWrap Placed (Resolved l),
    Deep.Traversable (Resolution l) (Abstract.FormalParameters l l) NodeWrap Placed (Resolved l),
    Deep.Traversable (Resolution l) (Abstract.ConstExpression l l) NodeWrap Placed (Resolved l)) =>
   Shallow.Traversable (Resolution l) NodeWrap Placed (Resolved l) (ProcedureHeading l l NodeWrap NodeWrap) where
   traverse res (Compose (pos, Ambiguous (proc@(ProcedureHeading _ _ parameters) :| []))) =
      StateT $ \s@(scope, state)->
         let innerScope = parameterScope `Map.union` scope
             parameterScope = case parameters
                              of Nothing -> mempty
                                 Just (Compose (_, Ambiguous (fp :| []))) | sections <- getFPSections fp
                                    -> Map.fromList (concatMap binding sections)
             binding (Compose (_, Ambiguous (section :| []))) = evalFPSection section $ \ _ names types->
                [(v, evalStateT (Deep.traverse res $ DeclaredVariable types) s) | v <- names]
         in Success ((pos, proc), (innerScope, state))
   traverse res (Compose (pos, Ambiguous (proc@(TypeBoundHeading _var receiverName receiverType _ _ parameters) :| []))) =
      StateT $ \s@(scope, state)->
         let innerScope = parameterScope `Map.union` receiverBinding `Map.union` scope
             receiverBinding :: Map Ident (Validation e (DeclarationRHS l f' Placed))
             receiverBinding = Map.singleton receiverName (Success $ DeclaredVariable $ (,) pos
                                                           $ Abstract.typeReference $ Abstract.nonQualIdent receiverType)
             parameterScope = case parameters
                              of Nothing -> mempty
                                 Just (Compose (_, Ambiguous (fp :| []))) | sections <- getFPSections fp
                                    -> Map.fromList (concatMap binding sections)
             binding (Compose (_, Ambiguous (section :| []))) = evalFPSection section $ \ _ names types->
                [(v, evalStateT (Deep.traverse res $ DeclaredVariable types) s) | v <- names]
         in Success ((pos, proc), (innerScope, state))

instance {-# overlaps #-}
   (BindableDeclaration l,
    Full.Traversable (Resolution l) (Abstract.Type l l) NodeWrap Placed (Resolved l),
    Full.Traversable (Resolution l) (Abstract.FormalParameters l l) NodeWrap Placed (Resolved l),
    Full.Traversable (Resolution l) (Abstract.ConstExpression l l) NodeWrap Placed (Resolved l),
    Deep.Traversable (Resolution l) (Abstract.Type l l) NodeWrap Placed (Resolved l),
    Deep.Traversable (Resolution l) (Abstract.FormalParameters l l) NodeWrap Placed (Resolved l),
    Deep.Traversable (Resolution l) (Abstract.ConstExpression l l) NodeWrap Placed (Resolved l)) =>
   Shallow.Traversable (Resolution l) NodeWrap Placed (Resolved l) (Block l l NodeWrap NodeWrap) where
   traverse res (Compose (pos, Ambiguous (body@(Block declarations _statements) :| []))) =
     StateT $ \(scope, state)-> Success ((pos, body), (localScope res "" declarations scope, state))
   traverse _ _ = StateT (const $ Failure $ pure AmbiguousParses)

instance {-# overlaps #-}
    (Deep.Traversable (Resolution l) (Abstract.Designator l l) NodeWrap Placed (Resolved l),
     Shallow.Traversable (Resolution l) NodeWrap Placed (Resolved l) (Abstract.Designator l l NodeWrap NodeWrap)) =>
    Shallow.Traversable (Resolution l) NodeWrap Placed (Resolved l) (Statement l l NodeWrap NodeWrap) where
   traverse res statements = StateT $ \s@(scope, _state)->
      let resolveStatement :: Statement l l NodeWrap NodeWrap
                            -> Validation (NonEmpty (Error l)) (Statement l l NodeWrap NodeWrap, ResolutionState)
          resolveStatement p@(ProcedureCall procedures _parameters) =
             case evalStateT (Shallow.traverse res procedures) s
             of Failure errors -> Failure errors
                Success{} -> pure (p, StatementState)
          resolveStatement stat = pure (stat, StatementState)
      in (\(pos, (r, s'))-> ((pos, r), (scope, s')))
         <$> unique InvalidStatement (AmbiguousStatement . (fst <$>)) (resolveStatement <$> statements)

mapResolveDefault :: Resolution l -> NodeWrap (g (Resolved l) (Resolved l)) -> Resolved l (g (Resolved l) (Resolved l))
mapResolveDefault Resolution{} (Compose (_, Ambiguous (x :| []))) = pure x
mapResolveDefault Resolution{} _ = StateT (const $ Failure $ pure AmbiguousParses)

traverseResolveDefault :: Resolution l -> NodeWrap (g (f :: * -> *) f) -> Resolved l (Placed (g f f))
traverseResolveDefault Resolution{} (Compose (pos, Ambiguous (x :| []))) = StateT (\s-> Success ((pos, x), s))
traverseResolveDefault Resolution{} _ = StateT (const $ Failure $ pure AmbiguousParses)

class Resolvable l where
   resolveDesignator :: Resolution l -> Scope l -> ResolutionState -> Designator l l NodeWrap NodeWrap
                     -> Validation (NonEmpty (Error l)) (Designator l l NodeWrap NodeWrap)
   resolveRecord :: Resolution l -> Scope l -> ResolutionState -> Designator l l NodeWrap NodeWrap
                 -> Validation (NonEmpty (Error l)) (Designator l l NodeWrap NodeWrap)

instance Resolvable Language where
   resolveDesignator res scope state (Variable q) =
      case resolveName res scope q
      of Failure err ->  Failure err
         Success DeclaredType{} | state /= ExpressionOrTypeState -> Failure (NotAValue q :| [])
         Success _ -> Success (Variable q)
   resolveDesignator res scope state d@(Field records field) =
      case evalStateT (Shallow.traverse res records) (scope, state)
      of Failure errors -> Failure errors
         Success{} -> pure d
   resolveDesignator res scope state (TypeGuard records subtypes) =
      case unique InvalidRecord AmbiguousRecord (resolveRecord res scope state <$> records)
      of Failure errors -> Failure errors
         Success{} -> TypeGuard records <$> resolveTypeName res scope subtypes
   resolveDesignator res scope state d@(Dereference pointers) =
      case evalStateT (Shallow.traverse res pointers) (scope, state)
      of Failure errors -> Failure errors
         Success{} -> pure d
   resolveDesignator _ _ _ d = pure d

   resolveRecord res scope state d@(Variable q) =
      case resolveName res scope q
      of Failure err -> Failure err
         Success DeclaredType{} -> Failure (NotAValue q :| [])
         Success DeclaredProcedure{} -> Failure (NotARecord q :| [])
         Success DeclaredVariable{} -> resolveDesignator res scope state d
   resolveRecord res scope state d = resolveDesignator res scope state d

resolveTypeName res scope q =
   case resolveName res scope q
   of Failure err ->  Failure err
      Success DeclaredType{} -> Success q
      Success _ -> Failure (NotAType q :| [])

resolveName :: (Abstract.Nameable l, Abstract.Oberon l)
            => Resolution l -> Scope l -> Abstract.QualIdent l
            -> Validation (NonEmpty (Error l)) (DeclarationRHS l Placed Placed)
resolveName res scope q
   | Just (moduleName, name) <- Abstract.getQualIdentNames q =
     case Map.lookup moduleName (_modules res)
     of Nothing -> Failure (UnknownModule q :| [])
        Just exports -> case Map.lookup name exports
                        of Just rhs -> rhs
                           Nothing -> Failure (UnknownImport q :| [])
   | Just name <- Abstract.getNonQualIdentName q =
     case Map.lookup name scope
     of Just (Success rhs) -> Success rhs
        _ -> Failure (UnknownLocal name :| [])

resolveModules :: forall l. (BindableDeclaration l, CoFormalParameters l, Abstract.Wirthy l,
                             Deep.Traversable (Resolution l) (Abstract.Declaration l l) NodeWrap Placed (Resolved l),
                             Deep.Traversable (Resolution l) (Abstract.Type l l) NodeWrap Placed (Resolved l),
                             Deep.Traversable (Resolution l) (Abstract.ProcedureHeading l l) NodeWrap Placed (Resolved l),
                             Deep.Traversable (Resolution l) (Abstract.FormalParameters l l) NodeWrap Placed (Resolved l),
                             Deep.Traversable (Resolution l) (Abstract.Expression l l) NodeWrap Placed (Resolved l),
                             Deep.Traversable (Resolution l) (Abstract.Block l l) NodeWrap Placed (Resolved l),
                             Deep.Traversable (Resolution l) (Abstract.StatementSequence l l) NodeWrap Placed (Resolved l),
                             Full.Traversable (Resolution l) (Abstract.Declaration l l) NodeWrap Placed (Resolved l),
                             Full.Traversable (Resolution l) (Abstract.Type l l) NodeWrap Placed (Resolved l),
                             Full.Traversable (Resolution l) (Abstract.ProcedureHeading l l) NodeWrap Placed (Resolved l),
                             Full.Traversable (Resolution l) (Abstract.FormalParameters l l) NodeWrap Placed (Resolved l),
                             Full.Traversable (Resolution l) (Abstract.Expression l l) NodeWrap Placed (Resolved l),
                             Full.Traversable (Resolution l) (Abstract.Block l l) NodeWrap Placed (Resolved l),
                             Full.Traversable (Resolution l) (Abstract.StatementSequence l l) NodeWrap Placed (Resolved l)) =>
                  Predefined l -> Map Ident (Module l l NodeWrap NodeWrap)
                -> Validation (NonEmpty (Ident, NonEmpty (Error l))) (Map Ident (Module l l Placed Placed))
resolveModules predefinedScope modules = traverseWithKey extractErrors modules'
   where modules' = resolveModule predefinedScope modules' <$> modules
         extractErrors moduleKey (Failure e)   = Failure ((moduleKey, e) :| [])
         extractErrors _         (Success mod) = Success mod

resolveModule :: forall l. (BindableDeclaration l,
                            Full.Traversable (Resolution l) (Abstract.Declaration l l) NodeWrap Placed (Resolved l),
                            Full.Traversable (Resolution l) (Abstract.Type l l) NodeWrap Placed (Resolved l),
                            Full.Traversable (Resolution l) (Abstract.FormalParameters l l) NodeWrap Placed (Resolved l),
                            Full.Traversable (Resolution l) (Abstract.ConstExpression l l) NodeWrap Placed (Resolved l),
                            Full.Traversable (Resolution l) (Abstract.StatementSequence l l) NodeWrap Placed (Resolved l),
                            Deep.Traversable (Resolution l) (Declaration l l) NodeWrap Placed (Resolved l),
                            Deep.Traversable (Resolution l) (Abstract.Declaration l l) NodeWrap Placed (Resolved l),
                            Deep.Traversable (Resolution l) (Abstract.StatementSequence l l) NodeWrap Placed (Resolved l),
                            Deep.Traversable (Resolution l) (Abstract.Type l l) NodeWrap Placed (Resolved l),
                            Deep.Traversable (Resolution l) (Abstract.FormalParameters l l) NodeWrap Placed (Resolved l),
                            Deep.Traversable (Resolution l) (Abstract.ConstExpression l l) NodeWrap Placed (Resolved l)) =>
                 Scope l -> Map Ident (Validation (NonEmpty (Error l)) (Module l l Placed Placed))
              -> Module l l NodeWrap NodeWrap -> Validation (NonEmpty (Error l)) (Module l l Placed Placed)
resolveModule predefined modules m@(Module moduleName imports declarations body) =
   evalStateT (Deep.traverse res m) (moduleGlobalScope, ModuleState)
   where res = Resolution moduleExports
         importedModules = Map.delete mempty (Map.mapKeysWith clashingRenames importedAs modules)
            where importedAs moduleName = case List.find ((== moduleName) . snd) imports
                                          of Just (Nothing, moduleKey) -> moduleKey
                                             Just (Just innerKey, _) -> innerKey
                                             Nothing -> mempty
                  clashingRenames _ _ = Failure (ClashingImports :| [])
         resolveDeclaration :: NodeWrap (Declaration l l NodeWrap NodeWrap) -> Resolved l (Declaration l l Placed Placed)
         resolveDeclaration d = snd <$> (traverse (Deep.traverse res) d >>= Shallow.traverse res)
         moduleExports = foldMap exportsOfModule <$> importedModules
         moduleGlobalScope = localScope res moduleName declarations predefined

localScope :: forall l. (BindableDeclaration l,
                         Full.Traversable (Resolution l) (Abstract.Type l l) NodeWrap Placed (Resolved l),
                         Full.Traversable (Resolution l) (Abstract.FormalParameters l l) NodeWrap Placed (Resolved l),
                         Full.Traversable (Resolution l) (Abstract.ConstExpression l l) NodeWrap Placed (Resolved l)) =>
              Resolution l -> Ident -> [NodeWrap (Abstract.Declaration l l NodeWrap NodeWrap)] -> Scope l -> Scope l
localScope res qual declarations outerScope = innerScope
   where innerScope = Map.union (snd <$> scopeAdditions) outerScope
         scopeAdditions = (resolveBinding res innerScope <$>)
                          <$> Map.fromList (concatMap (declarationBinding qual . unamb) declarations)
         unamb (Compose (offset, Ambiguous (x :| []))) = x
         resolveBinding     :: Resolution l -> Scope l -> DeclarationRHS l NodeWrap NodeWrap
                            -> Validation (NonEmpty (Error l)) (DeclarationRHS l Placed Placed)
         resolveBinding res scope dr = evalStateT (Deep.traverse res dr) (scope, DeclarationState)

class BindableDeclaration l where
   declarationBinding :: Foldable f => Ident -> Abstract.Declaration l l f f -> [(Ident, (AccessMode, DeclarationRHS l f f))]
   
instance BindableDeclaration Language where
   declarationBinding _ (ConstantDeclaration (IdentDef name export) expr) =
      [(name, (export, DeclaredConstant expr))]
   declarationBinding _ (TypeDeclaration (IdentDef name export) typeDef) =
      [(name, (export, DeclaredType typeDef))]
   declarationBinding _ (VariableDeclaration names typeDef) =
      [(name, (export, DeclaredVariable typeDef)) | (IdentDef name export) <- NonEmpty.toList names]
   declarationBinding moduleName (ProcedureDeclaration heading _) = procedureHeadBinding (foldr1 const heading)
      where procedureHeadBinding (ProcedureHeading _ (IdentDef name export) parameters) =
               [(name, (export, DeclaredProcedure (moduleName == "SYSTEM") parameters))]
            procedureHeadBinding (TypeBoundHeading _ _ _ _ (IdentDef name export) parameters) =
               [(name, (export, DeclaredProcedure (moduleName == "SYSTEM") parameters))]
   declarationBinding _ (ForwardDeclaration (IdentDef name export) parameters) =
      [(name, (export, DeclaredProcedure False parameters))]

predefined, predefined2 :: Abstract.Oberon l => Predefined l
-- | The set of 'Predefined' types and procedures defined in the Oberon Language Report.
predefined = Success <$> Map.fromList
   [("BOOLEAN", DeclaredType ((,) 0 $ Abstract.typeReference $ Abstract.nonQualIdent "BOOLEAN")),
    ("CHAR", DeclaredType ((,) 0 $ Abstract.typeReference $ Abstract.nonQualIdent "CHAR")),
    ("SHORTINT", DeclaredType ((,) 0 $ Abstract.typeReference $ Abstract.nonQualIdent "SHORTINT")),
    ("INTEGER", DeclaredType ((,) 0 $ Abstract.typeReference $ Abstract.nonQualIdent "INTEGER")),
    ("LONGINT", DeclaredType ((,) 0 $ Abstract.typeReference $ Abstract.nonQualIdent "LONGINT")),
    ("REAL", DeclaredType ((,) 0 $ Abstract.typeReference $ Abstract.nonQualIdent "REAL")),
    ("LONGREAL", DeclaredType ((,) 0 $ Abstract.typeReference $ Abstract.nonQualIdent "LONGREAL")),
    ("SET", DeclaredType ((,) 0 $ Abstract.typeReference $ Abstract.nonQualIdent "SET")),
    ("TRUE", DeclaredConstant ((,) 0 $ Abstract.read $ (,) 0 $ Abstract.variable $ Abstract.nonQualIdent "TRUE")),
    ("FALSE", DeclaredConstant ((,) 0 $ Abstract.read $ (,) 0 $ Abstract.variable $ Abstract.nonQualIdent "FALSE")),
    ("ABS", DeclaredProcedure False $ Just $ (,) 0 $
            Abstract.formalParameters [(,) 0 $ Abstract.fpSection False (pure "n") $ (,) 0
                                       $ Abstract.typeReference $ Abstract.nonQualIdent "INTEGER"] $
            Just $ Abstract.nonQualIdent "INTEGER"),
    ("ASH", DeclaredProcedure False $ Just $ (,) 0 $
            Abstract.formalParameters [(,) 0 $ Abstract.fpSection False (pure "n") $ (,) 0
                                       $ Abstract.typeReference $ Abstract.nonQualIdent "INTEGER"] $
            Just $ Abstract.nonQualIdent "INTEGER"),
    ("CAP", DeclaredProcedure False $ Just $ (,) 0 $
            Abstract.formalParameters [(,) 0 $ Abstract.fpSection False (pure "c") $ (,) 0
                                       $ Abstract.typeReference $ Abstract.nonQualIdent "CHAR"] $
            Just $ Abstract.nonQualIdent "CHAR"),
    ("LEN", DeclaredProcedure False $ Just $ (,) 0 $
            Abstract.formalParameters [(,) 0 $ Abstract.fpSection False (pure "c") $ (,) 0
                                       $ Abstract.typeReference $ Abstract.nonQualIdent "ARRAY"] $
            Just $ Abstract.nonQualIdent "LONGINT"),
    ("MAX", DeclaredProcedure True $ Just $ (,) 0 $
            Abstract.formalParameters [(,) 0 $ Abstract.fpSection False (pure "c") $ (,) 0
                                       $ Abstract.typeReference $ Abstract.nonQualIdent "SET"] $
            Just $ Abstract.nonQualIdent "INTEGER"),
    ("MIN", DeclaredProcedure True $ Just $ (,) 0 $
            Abstract.formalParameters [(,) 0 $ Abstract.fpSection False (pure "c") $ (,) 0
                                       $ Abstract.typeReference $ Abstract.nonQualIdent "SET"] $
            Just $ Abstract.nonQualIdent "INTEGER"),
    ("ODD", DeclaredProcedure False $ Just $ (,) 0 $
            Abstract.formalParameters [(,) 0 $ Abstract.fpSection False (pure "n") $ (,) 0
                                       $ Abstract.typeReference $ Abstract.nonQualIdent "CHAR"] $
            Just $ Abstract.nonQualIdent "BOOLEAN"),
    ("SIZE", DeclaredProcedure True $ Just $ (,) 0 $
             Abstract.formalParameters [(,) 0 $ Abstract.fpSection False (pure "n") $ (,) 0
                                        $ Abstract.typeReference $ Abstract.nonQualIdent "CHAR"] $
             Just $ Abstract.nonQualIdent "INTEGER"),
    ("ORD", DeclaredProcedure False $ Just $ (,) 0 $
            Abstract.formalParameters [(,) 0 $ Abstract.fpSection False (pure "n") $ (,) 0
                                       $ Abstract.typeReference $ Abstract.nonQualIdent "CHAR"] $
            Just $ Abstract.nonQualIdent "INTEGER"),
    ("CHR", DeclaredProcedure False $ Just $ (,) 0 $
            Abstract.formalParameters [(,) 0 $ Abstract.fpSection False (pure "n") $ (,) 0
                                       $ Abstract.typeReference $ Abstract.nonQualIdent "INTEGER"] $
            Just $ Abstract.nonQualIdent "CHAR"),
    ("SHORT", DeclaredProcedure False $ Just $ (,) 0 $
              Abstract.formalParameters [(,) 0 $ Abstract.fpSection False (pure "n") $ (,) 0
                                         $ Abstract.typeReference $ Abstract.nonQualIdent "INTEGER"] $
              Just $ Abstract.nonQualIdent "INTEGER"),
    ("LONG", DeclaredProcedure False $ Just $ (,) 0 $
             Abstract.formalParameters [(,) 0 $ Abstract.fpSection False (pure "n") $ (,) 0
                                        $ Abstract.typeReference $ Abstract.nonQualIdent "INTEGER"] $
             Just $ Abstract.nonQualIdent "INTEGER"),
    ("ENTIER", DeclaredProcedure False $ Just $ (,) 0 $
               Abstract.formalParameters [(,) 0 $ Abstract.fpSection False (pure "n") $ (,) 0
                                          $ Abstract.typeReference $ Abstract.nonQualIdent "REAL"] $
               Just $ Abstract.nonQualIdent "INTEGER"),
    ("INC", DeclaredProcedure False $ Just $ (,) 0 $
            Abstract.formalParameters [(,) 0 $ Abstract.fpSection False (pure "n") $ (,) 0
                                       $ Abstract.typeReference $ Abstract.nonQualIdent "INTEGER"] Nothing),
    ("DEC", DeclaredProcedure False $ Just $ (,) 0 $
            Abstract.formalParameters [(,) 0 $ Abstract.fpSection False (pure "n") $ (,) 0
                                       $ Abstract.typeReference $ Abstract.nonQualIdent "INTEGER"] Nothing),
    ("INCL", DeclaredProcedure False $ Just $ (,) 0 $
             Abstract.formalParameters [(,) 0 $ Abstract.fpSection False (pure "s") $ (,) 0
                                        $ Abstract.typeReference $ Abstract.nonQualIdent "SET",
                               (,) 0 $ Abstract.fpSection False (pure "n") $ (,) 0
                               $ Abstract.typeReference $ Abstract.nonQualIdent "INTEGER"] Nothing),
    ("EXCL", DeclaredProcedure False $ Just $ (,) 0 $
             Abstract.formalParameters [(,) 0 $ Abstract.fpSection False (pure "s") $ (,) 0
                                        $ Abstract.typeReference $ Abstract.nonQualIdent "SET",
                               (,) 0 $ Abstract.fpSection False (pure "n") $ (,) 0
                               $ Abstract.typeReference $ Abstract.nonQualIdent "INTEGER"] Nothing),
    ("COPY", DeclaredProcedure False $ Just $ (,) 0 $
             Abstract.formalParameters [(,) 0 $ Abstract.fpSection False (pure "s") $ (,) 0
                                        $ Abstract.typeReference $ Abstract.nonQualIdent "ARRAY",
                               (,) 0 $ Abstract.fpSection False (pure "n") $ (,) 0
                               $ Abstract.typeReference $ Abstract.nonQualIdent "ARRAY"] Nothing),
    ("NEW", DeclaredProcedure False $ Just $ (,) 0 $
            Abstract.formalParameters [(,) 0 $ Abstract.fpSection False (pure "n") $ (,) 0
                                       $ Abstract.typeReference $ Abstract.nonQualIdent "POINTER"] Nothing),
    ("HALT", DeclaredProcedure False $ Just $ (,) 0 $
             Abstract.formalParameters [(,) 0 $ Abstract.fpSection False (pure "n") $ (,) 0
                                        $ Abstract.typeReference $ Abstract.nonQualIdent "INTEGER"] Nothing)]

-- | The set of 'Predefined' types and procedures defined in the Oberon-2 Language Report.
predefined2 = predefined <>
   (Success <$> Map.fromList
    [("ASSERT",
      DeclaredProcedure False $ Just $ (,) 0 $ Abstract.formalParameters
       [(,) 0 $ Abstract.fpSection False (pure "s") $ (,) 0 $ Abstract.typeReference $ Abstract.nonQualIdent "ARRAY",
        (,) 0 $ Abstract.fpSection False (pure "n") $ (,) 0 $ Abstract.typeReference $ Abstract.nonQualIdent "ARRAY"]
      Nothing)])

exportsOfModule :: BindableDeclaration l => Module l l Placed Placed -> Scope l
exportsOfModule = fmap Success . Map.mapMaybe isExported . globalsOfModule
   where isExported (PrivateOnly, _) = Nothing
         isExported (_, binding) = Just binding

globalsOfModule :: BindableDeclaration l => Module l l Placed Placed -> Map Ident (AccessMode, DeclarationRHS l Placed Placed)
globalsOfModule (Module name imports declarations _) =
   Map.fromList (concatMap (declarationBinding name . snd) declarations)

unique :: (NonEmpty (Error l) -> Error l) -> ([a] -> Error l) -> NodeWrap (Validation (NonEmpty (Error l)) a)
       -> Validation (NonEmpty (Error l)) (Placed a)
unique _ _ (Compose (pos, Ambiguous (x :| []))) = (,) pos <$> x
unique inv amb (Compose (pos, Ambiguous xs)) =
   case partitionEithers (validationToEither <$> NonEmpty.toList xs)
   of (_, [x]) -> Success (pos, x)
      (errors, []) -> Failure (inv (sconcat $ NonEmpty.fromList errors) :| [])
      (_, multi) -> Failure (amb multi :| [])

$(Rank2.TH.deriveFunctor ''DeclarationRHS)
$(Rank2.TH.deriveFoldable ''DeclarationRHS)
$(Rank2.TH.deriveTraversable ''DeclarationRHS)
$(Transformation.Deep.TH.deriveTraversable ''DeclarationRHS)

instance (Deep.Traversable (Resolution l) (Declaration l l) NodeWrap Placed (Resolved l),
          Shallow.Traversable (Resolution l) NodeWrap Placed (Resolved l) (Declaration l l NodeWrap NodeWrap)) =>
         Full.Traversable (Resolution l) (Declaration l l) NodeWrap Placed (Resolved l) where
  traverse = Full.traverseDownDefault

instance Deep.Traversable (Resolution l) (Type l l) NodeWrap Placed (Resolved l) =>
         Full.Traversable (Resolution l) (Type l l) NodeWrap Placed (Resolved l) where
  traverse = Full.traverseDownDefault

instance Deep.Traversable (Resolution l) (FieldList l l) NodeWrap Placed (Resolved l) =>
         Full.Traversable (Resolution l) (FieldList l l) NodeWrap Placed (Resolved l) where
  traverse = Full.traverseDownDefault

instance (Deep.Traversable (Resolution l) (ProcedureHeading l l) NodeWrap Placed (Resolved l),
          Shallow.Traversable (Resolution l) NodeWrap Placed (Resolved l) (ProcedureHeading l l NodeWrap NodeWrap)) =>
         Full.Traversable (Resolution l) (ProcedureHeading l l) NodeWrap Placed (Resolved l) where
  traverse = Full.traverseDownDefault

instance Deep.Traversable (Resolution l) (FormalParameters l l) NodeWrap Placed (Resolved l) => Full.Traversable (Resolution l) (FormalParameters l l) NodeWrap Placed (Resolved l) where
  traverse = Full.traverseDownDefault

instance Deep.Traversable (Resolution l) (FPSection l l) NodeWrap Placed (Resolved l) => Full.Traversable (Resolution l) (FPSection l l) NodeWrap Placed (Resolved l) where
  traverse = Full.traverseDownDefault

instance (Deep.Traversable (Resolution l) (Expression l l) NodeWrap Placed (Resolved l),
          Shallow.Traversable (Resolution l) NodeWrap Placed (Resolved l) (Expression l l NodeWrap NodeWrap)) =>
         Full.Traversable (Resolution l) (Expression l l) NodeWrap Placed (Resolved l) where
  traverse = Full.traverseDownDefault

instance (Deep.Traversable (Resolution l) (Block l l) NodeWrap Placed (Resolved l),
          Shallow.Traversable (Resolution l) NodeWrap Placed (Resolved l) (Block l l NodeWrap NodeWrap)) =>
         Full.Traversable (Resolution l) (Block l l) NodeWrap Placed (Resolved l) where
  traverse = Full.traverseDownDefault

instance Deep.Traversable (Resolution l) (StatementSequence l l) NodeWrap Placed (Resolved l) => Full.Traversable (Resolution l) (StatementSequence l l) NodeWrap Placed (Resolved l) where
  traverse = Full.traverseDownDefault

instance (Deep.Traversable (Resolution l) (Statement l l) NodeWrap Placed (Resolved l),
          Shallow.Traversable (Resolution l) NodeWrap Placed (Resolved l) (Statement l l NodeWrap NodeWrap)) =>
         Full.Traversable (Resolution l) (Statement l l) NodeWrap Placed (Resolved l) where
  traverse = Full.traverseDownDefault

instance Deep.Traversable (Resolution l) (Deep.Product (Expression l l) (StatementSequence l l)) NodeWrap Placed (Resolved l) => Full.Traversable (Resolution l) (Deep.Product (Expression l l) (StatementSequence l l)) NodeWrap Placed (Resolved l) where
  traverse = Full.traverseDownDefault

instance Deep.Traversable (Resolution l) (Case l l) NodeWrap Placed (Resolved l) => Full.Traversable (Resolution l) (Case l l) NodeWrap Placed (Resolved l) where
  traverse = Full.traverseDownDefault

instance Deep.Traversable (Resolution l) (CaseLabels l l) NodeWrap Placed (Resolved l) => Full.Traversable (Resolution l) (CaseLabels l l) NodeWrap Placed (Resolved l) where
  traverse = Full.traverseDownDefault

instance Deep.Traversable (Resolution l) (WithAlternative l l) NodeWrap Placed (Resolved l) => Full.Traversable (Resolution l) (WithAlternative l l) NodeWrap Placed (Resolved l) where
  traverse = Full.traverseDownDefault

instance (Deep.Traversable (Resolution l) (Designator l l) NodeWrap Placed (Resolved l), Resolvable l) => Full.Traversable (Resolution l) (Designator l l) NodeWrap Placed (Resolved l) where
  traverse = Full.traverseDownDefault

instance Deep.Traversable (Resolution l) (Element l l) NodeWrap Placed (Resolved l) => Full.Traversable (Resolution l) (Element l l) NodeWrap Placed (Resolved l) where
  traverse = Full.traverseDownDefault

instance Deep.Traversable (Resolution l) (Value l l) NodeWrap Placed (Resolved l) => Full.Traversable (Resolution l) (Value l l) NodeWrap Placed (Resolved l) where
  traverse = Full.traverseDownDefault
