{-# LANGUAGE PackageImports, TypeSynonymInstances, FlexibleInstances #-}
module Gencot.Util.Types where

import Data.Set as S
--import Control.Monad (liftM)
import Data.Foldable (find)

import Language.C.Analysis as LCA
import Language.C.Data.Ident as LCI
import qualified Language.C.Analysis.DefTable as LCD
import Language.C.Analysis.TravMonad (Trav,MonadSymtab)

collectUsedTypes :: LCA.DeclEvent -> Trav (Set LCA.Type) ()
collectUsedTypes _ = return ()

transCloseUsedTypes :: LCA.GlobalDecls -> Set LCA.Type -> Set LCA.Type
transCloseUsedTypes _ _ = S.empty

getUsedTypes :: LCA.DeclEvent -> Set LCA.Type
getUsedTypes _ = S.empty

isLinearType :: MonadSymtab m => LCA.Type -> m Bool
isLinearType td@(LCA.TypeDefType _ _ _) = isLinearType $ resolveTypedef td
isLinearType (LCA.PtrType t _ _) = return $ not $ isFunction t
isLinearType (LCA.ArrayType t _ _ _) = isLinearType t
isLinearType (LCA.DirectType (LCA.TyComp (LCA.CompTypeRef sueref _ _)) _ _) = do
    table <- LCA.getDefTable
    let (Just tagentry) = LCD.lookupTag sueref table
    case tagentry of
         Left _ -> return False
         Right (LCA.CompDef (LCA.CompType _ _ mdecls _ _)) -> do
             h <- mapM (isLinearType . LCA.declType) mdecls
             return $ all id h
isLinearType _ = return False

isLinearParType :: MonadSymtab m => LCA.Type -> m Bool
isLinearParType t = if isArray t then return True else isLinearType t

isReadOnlyType :: MonadSymtab m => LCA.Type -> m Bool
isReadOnlyType td@(LCA.TypeDefType _ _ _) = isReadOnlyType $ resolveTypedef td
isReadOnlyType (LCA.PtrType t _ _) = 
    if isFunction t 
       then return True
       else if isConstQualified t 
            then isReadOnlyType t
            else return False
isReadOnlyType (LCA.ArrayType t _ _ _) = isReadOnlyType t
isReadOnlyType (LCA.FunctionType _ _) = return True
isReadOnlyType (LCA.DirectType (LCA.TyComp (LCA.CompTypeRef sueref _ _)) _ _) = do
    table <- LCA.getDefTable
    let (Just tagentry) = LCD.lookupTag sueref table
    case tagentry of
         Left _ -> return False
         Right (LCA.CompDef (LCA.CompType _ _ mdecls _ _)) -> do
             h <- mapM (isReadOnlyType . LCA.declType) mdecls
             return $ all id h
isReadOnlyType (LCA.DirectType _ _ _) = return True

isReadOnlyParType :: MonadSymtab m => LCA.Type -> m Bool
isReadOnlyParType (LCA.ArrayType t _ _ _) = 
    if isFunction t 
       then return True
       else if isConstQualified t 
            then isReadOnlyType t
            else return False
isReadOnlyParType t = isReadOnlyType t

isConstQualified :: LCA.Type -> Bool
isConstQualified (LCA.TypeDefType (LCA.TypeDefRef _ t _) tq _) = constant tq || isConstQualified t
isConstQualified (LCA.PtrType _ tq _) = constant tq
isConstQualified (LCA.ArrayType _ _ tq _) = constant tq
isConstQualified (LCA.FunctionType _ _) = False
isConstQualified (LCA.DirectType _ tq _) = constant tq

isAggOrFunc :: LCA.Type -> Bool
isAggOrFunc t = isAggregate t || isFunction t

isFunPointer :: LCA.Type -> Bool
isFunPointer td@(LCA.TypeDefType _ _ _) = isFunPointer $ resolveTypedef td
isFunPointer (LCA.PtrType t _ _) = isFunction t
isFunPointer _ = False

isFunction :: LCA.Type -> Bool
isFunction td@(LCA.TypeDefType _ _ _) = isFunction $ resolveTypedef td
isFunction (LCA.FunctionType _ _) = True
isFunction _ = False

isPointer :: LCA.Type -> Bool
isPointer td@(LCA.TypeDefType _ _ _) = isPointer $ resolveTypedef td
isPointer (LCA.PtrType _ _ _) = True
isPointer _ = False

isArray :: LCA.Type -> Bool
isArray td@(LCA.TypeDefType _ _ _) = isArray $ resolveTypedef td
isArray (LCA.ArrayType _ _ _ _) = True
isArray _ = False

isAggregate :: LCA.Type -> Bool
isAggregate td@(LCA.TypeDefType _ _ _) = isAggregate $ resolveTypedef td
isAggregate (LCA.DirectType (LCA.TyComp _) _ _) = True
isAggregate (LCA.ArrayType _ _ _ _) = True
isAggregate _ = False

resolveTypedef :: LCA.Type -> LCA.Type
resolveTypedef (LCA.TypeDefType (LCA.TypeDefRef _ t _) _ _) = resolveTypedef t
resolveTypedef t = t

getPointedType :: LCA.Type -> LCA.Type
getPointedType t | isPointer t = rt
    where (LCA.PtrType rt _ _) = resolveTypedef t
getPointedType _ = error "No pointer type passed to getPointedType"

getFunType :: LCA.Type -> LCA.FunType
getFunType t | isFunction t = rt
    where (LCA.FunctionType rt _) = resolveTypedef t
getFunType _ = error "No function type passed to getFunType"

getCompType :: LCA.Type -> LCD.DefTable -> LCA.CompType
getCompType (LCA.DirectType (LCA.TyComp (LCA.CompTypeRef sueref _ _)) _ _) dt = ctype
    where (Just (Right (LCA.CompDef ctype))) = LCD.lookupTag sueref dt
getCompType (LCA.PtrType typ _ _) dt = getCompType typ dt
getCompType (LCA.TypeDefType (LCA.TypeDefRef _ typ _) _ _) dt = getCompType typ dt

getMemberDecl :: LCA.CompType -> LCI.Ident -> Maybe LCA.MemberDecl
getMemberDecl (LCA.CompType _ _ mdecls _ _) mid = find (hasMemberName mid) mdecls

hasMemberName :: LCI.Ident -> LCA.MemberDecl -> Bool
hasMemberName nam dec = 
    case LCA.getVarDecl dec of
         (LCA.VarDecl (LCA.VarName dnam _) _ _) -> nam == dnam
         _ -> False
