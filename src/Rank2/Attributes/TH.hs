-- | This module exports the templates for automatic instance deriving of "Rank2.Attributes" type classes. The most
-- common way to use it would be
--
-- > import qualified Rank2.Attributes.TH
-- > data MyDataType f' f = ...
-- > $(Rank2.Attributes.TH.deriveDeepTransformation ''MyDataType)
--

{-# Language TemplateHaskell #-}
-- Adapted from https://wiki.haskell.org/A_practical_Template_Haskell_Tutorial

module Rank2.Attributes.TH (deriveAll, deriveDeepTransformation)
where

import Control.Monad (replicateM)
import Language.Haskell.TH
import Language.Haskell.TH.Syntax (BangType, VarBangType, getQ, putQ)

import qualified Rank2.Attributes
import qualified Rank2.TH


data Deriving = Deriving { _constructor :: Name, _variableN :: Name, _variable1 :: Name }

deriveAll :: Name -> Q [Dec]
deriveAll ty = foldr f (pure []) [Rank2.TH.deriveFunctor, Rank2.TH.deriveFoldable, Rank2.TH.deriveTraversable,
                                  deriveDeepTransformation]
   where f derive rest = (<>) <$> derive ty <*> rest

deriveDeepTransformation :: Name -> Q [Dec]
deriveDeepTransformation ty = do
   t <- varT <$> newName "t"
   p <- varT <$> newName "p"
   q <- varT <$> newName "q"
   let deepConstraint ty = conT ''Rank2.Attributes.DeepTransformation `appT` t `appT` ty `appT` p `appT` q
       shallowConstraint ty =
          conT ''Rank2.Attributes.Transformation `appT` t `appT` p `appT` q `appT` (ty `appT` q `appT` q)
   (instanceType, cs) <- reifyConstructors ty
   (constraints, dec) <- genDeepmap deepConstraint shallowConstraint cs
   sequence [instanceD (cxt (appT (conT ''Functor) p : map pure constraints))
                       (deepConstraint instanceType)
                       [pure dec]]

reifyConstructors :: Name -> Q (TypeQ, [Con])
reifyConstructors ty = do
   (TyConI tyCon) <- reify ty
   (tyConName, tyVars, _kind, cs) <- case tyCon of
      DataD _ nm tyVars kind cs _   -> return (nm, tyVars, kind, cs)
      NewtypeD _ nm tyVars kind c _ -> return (nm, tyVars, kind, [c])
      _ -> fail "deriveApply: tyCon may not be a type synonym."

   let (KindedTV tyVar  (AppT (AppT ArrowT StarT) StarT) :
        KindedTV tyVar' (AppT (AppT ArrowT StarT) StarT) : _) = reverse tyVars
       instanceType           = foldl apply (conT tyConName) (reverse $ drop 2 $ reverse tyVars)
       apply t (PlainTV name)    = appT t (varT name)
       apply t (KindedTV name _) = appT t (varT name)

   putQ (Deriving tyConName tyVar' tyVar)
   return (instanceType, cs)

genDeepmap :: (Q Type -> Q Type) -> (Q Type -> Q Type) -> [Con] -> Q ([Type], Dec)
genDeepmap deepConstraint shallowConstraint cs = do
   (constraints, clauses) <- unzip <$> mapM (genDeepmapClause deepConstraint shallowConstraint) cs
   return (concat constraints, FunD 'Rank2.Attributes.deepmap clauses)

genDeepmapClause :: (Q Type -> Q Type) -> (Q Type -> Q Type) -> Con -> Q ([Type], Clause)
genDeepmapClause deepConstraint shallowConstraint (NormalC name fieldTypes) = do
   t          <- newName "t"
   fieldNames <- replicateM (length fieldTypes) (newName "x")
   let pats = [varP t, parensP (conP name $ map varP fieldNames)]
       constraintsAndFields = zipWith newField fieldNames fieldTypes
       newFields = map (snd <$>) constraintsAndFields
       body = normalB $ appsE $ conE name : newFields
       newField :: Name -> BangType -> Q ([Type], Exp)
       newField x (_, fieldType) = genDeepmapField (varE t) fieldType deepConstraint shallowConstraint (varE x) id
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> clause pats body []
genDeepmapClause deepConstraint shallowConstraint (RecC name fields) = do
   f <- newName "f"
   x <- newName "x"
   let body = normalB $ recConE name $ (snd <$>) <$> constraintsAndFields
       constraintsAndFields = map newNamedField fields
       newNamedField :: VarBangType -> Q ([Type], (Name, Exp))
       newNamedField (fieldName, _, fieldType) =
          ((,) fieldName <$>)
          <$> genDeepmapField (varE f) fieldType deepConstraint shallowConstraint (appE (varE fieldName) (varE x)) id
   constraints <- (concat . (fst <$>)) <$> sequence constraintsAndFields
   (,) constraints <$> clause [varP f, varP x] body []

genDeepmapField :: Q Exp -> Type -> (Q Type -> Q Type) -> (Q Type -> Q Type) -> Q Exp -> (Q Exp -> Q Exp)
                -> Q ([Type], Exp)
genDeepmapField trans fieldType deepConstraint shallowConstraint fieldAccess wrap = do
   Just (Deriving _ typeVarN typeVar1) <- getQ
   case fieldType of
     AppT ty (AppT (AppT con v1) v2) | ty == VarT typeVar1, v1 == VarT typeVarN, v2 == VarT typeVarN ->
        (,) <$> ((:) <$> deepConstraint (pure con) <*> ((:[]) <$> shallowConstraint (pure con)))
            <*> appE (wrap [| (Rank2.Attributes.remap $trans . (Rank2.Attributes.deepmap $trans <$>)) |]) fieldAccess
     AppT ty _  | ty == VarT typeVar1 ->
                  (,) [] <$> (wrap (varE 'Rank2.Attributes.remap `appE` trans) `appE` fieldAccess)
     AppT (AppT con v1) v2  | v1 == VarT typeVarN, v2 == VarT typeVar1 ->
        (,) <$> ((:[]) <$> deepConstraint (pure con))
            <*> appE (wrap [| Rank2.Attributes.deepmap $trans |]) fieldAccess
     AppT t1 t2 | t1 /= VarT typeVar1 ->
        genDeepmapField trans t2 deepConstraint shallowConstraint fieldAccess (wrap . appE (varE '(<$>)))
     SigT ty _kind -> genDeepmapField trans ty deepConstraint shallowConstraint fieldAccess wrap
     ParensT ty -> genDeepmapField trans ty deepConstraint shallowConstraint fieldAccess wrap
     _ -> (,) [] <$> fieldAccess
