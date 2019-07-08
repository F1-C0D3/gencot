{-# LANGUAGE PackageImports, TypeSynonymInstances, FlexibleInstances #-}
module Gencot.Util.Types where

import Data.List (nub,(\\))
import Data.Foldable (find)

import Language.C.Analysis as LCA
import Language.C.Data.Ident as LCI
import qualified Language.C.Analysis.DefTable as LCD
import Language.C.Analysis.TravMonad (Trav,MonadSymtab)

import Gencot.Util.Equality

collectUsedTypes :: LCA.DeclEvent -> Trav [LCA.Type] ()
collectUsedTypes _ = return ()

-- | As implementation for a set of types we use lists and the "set operations" defined for lists.
-- The types in a TypeSet must be unique.
-- The equality for types is defined in Gencot.Util.Equality.
-- For using Set LCA.Type an additional compare operation would be required.
type TypeSet = [LCA.Type]

-- | Function which selects a type set from a type.
type TypeSelector = LCA.Type -> TypeSet

-- | A type predicate
type TypePred = LCA.Type -> Bool

-- | Types occurring in a DeclEvent, filtered by a Type predicate.
-- In a type or tag definition it is the defined type.
-- In a declaration it is the type of the declared entity.
-- The result is always a singleton list or empty.
occurringTypes :: TypePred -> LCA.DeclEvent -> TypeSet
occurringTypes flt (LCA.TagEvent (LCA.CompDef (LCA.CompType r k _ attr n))) = 
    considerType flt $ LCA.DirectType (LCA.TyComp (LCA.CompTypeRef r k n)) LCA.noTypeQuals attr
occurringTypes flt (LCA.TagEvent (LCA.EnumDef (LCA.EnumType r _ attr n))) = 
    considerType flt $ LCA.DirectType (LCA.TyEnum (LCA.EnumTypeRef r n)) LCA.noTypeQuals attr
occurringTypes flt (LCA.DeclEvent decl) = declTypes flt decl
occurringTypes flt (LCA.ParamEvent decl) = declTypes flt decl
occurringTypes flt (LCA.LocalEvent decl) = declTypes flt decl
occurringTypes flt (LCA.TypeDefEvent (LCA.TypeDef nam t attrs n)) =
    considerType flt $ LCA.TypeDefType (LCA.TypeDefRef nam t n) LCA.noTypeQuals attrs
occurringTypes flt (LCA.AsmEvent _) = []

-- | Type selector combination.
-- The result is the union of the sets selected by the combined selectors.
unionTypeSelector :: [TypeSelector] -> TypeSelector
unionTypeSelector ts t = nub $ concat (ts <*> [t])

-- | Transitive closure of a type selector, applied to a set of types
transCloseTypes :: TypeSelector -> TypeSet -> TypeSet
transCloseTypes ts types =
    if null ct then types else transCloseTypes ts (ct ++ types)
    where ct = (nub $ concat $ map ts types) \\ types

-- | Select a type based on a type predicate.
considerType :: TypePred -> TypeSelector
considerType flt t = if flt t then [t] else []

-- | Select the type from a declaration, based on a type predicate.
declTypes :: LCA.Declaration d => TypePred -> d -> TypeSet
declTypes flt decl = considerType flt $ LCA.declType decl

-- | Type selector which resolves type definitions, with additional result filter.
selInTypeDef :: TypePred -> TypeSelector
selInTypeDef flt (LCA.TypeDefType (LCA.TypeDefRef _ t _) _ _) = considerType flt t
selInTypeDef _ _ = []

-- | Type selector for the base type of a pointer or array type, with additional result filter.
selInDerived :: TypePred -> TypeSelector
selInDerived flt (LCA.PtrType t _ _) = considerType flt t
selInDerived flt (LCA.ArrayType t _ _ _) = considerType flt t
selInDerived _ _ = []

-- | Type selector for the result and parameter types of a function type, with additional result filter.
selInFunction :: TypePred -> TypeSelector
selInFunction flt (LCA.FunctionType (LCA.FunType rt pars _) _) =
    nub (if flt rt then rt:pts else pts)
    where pts = concat $ map (declTypes flt) pars
selInFunction flt (LCA.FunctionType (LCA.FunTypeIncomplete rt) _) = considerType flt rt
selInFunction _ _ = []

-- | Type selector for the member types of composite types, with additional result filter.
-- Needs a symbol table to look up the tag definitions.
selInComp :: LCD.DefTable -> TypePred -> TypeSelector
selInComp dt flt (LCA.DirectType (LCA.TyComp (LCA.CompTypeRef ref _ _)) _ _) =
    case LCD.lookupTag ref dt of 
         Nothing -> []
         Just (Left _) -> []
         Just (Right (LCA.CompDef (LCA.CompType _ _ mems _ _))) ->
            nub $ concat $ map (declTypes flt) mems
selInComp _ _ _ = []

-- | Type selector for all types referenced in the given types, with additional result filter.
selInAllTypes :: LCD.DefTable -> TypePred -> TypeSelector
selInAllTypes dt p = unionTypeSelector [selInTypeDef p,selInDerived p,selInFunction p,selInComp dt p]

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

isConstQualified :: TypePred
isConstQualified (LCA.TypeDefType (LCA.TypeDefRef _ t _) tq _) = constant tq || isConstQualified t
isConstQualified (LCA.PtrType _ tq _) = constant tq
isConstQualified (LCA.ArrayType _ _ tq _) = constant tq
isConstQualified (LCA.FunctionType _ _) = False
isConstQualified (LCA.DirectType _ tq _) = constant tq

isAggOrFunc :: TypePred
isAggOrFunc t = isAggregate t || isFunction t

isFunPointer :: TypePred
isFunPointer td@(LCA.TypeDefType _ _ _) = isFunPointer $ resolveTypedef td
isFunPointer (LCA.PtrType t _ _) = isFunction t
isFunPointer _ = False

isFunction :: TypePred
isFunction td@(LCA.TypeDefType _ _ _) = isFunction $ resolveTypedef td
isFunction (LCA.FunctionType _ _) = True
isFunction _ = False

isPointer :: TypePred
isPointer td@(LCA.TypeDefType _ _ _) = isPointer $ resolveTypedef td
isPointer (LCA.PtrType _ _ _) = True
isPointer _ = False

isArray :: TypePred
isArray td@(LCA.TypeDefType _ _ _) = isArray $ resolveTypedef td
isArray (LCA.ArrayType _ _ _ _) = True
isArray _ = False

isAggregate :: TypePred
isAggregate td@(LCA.TypeDefType _ _ _) = isAggregate $ resolveTypedef td
isAggregate (LCA.DirectType (LCA.TyComp _) _ _) = True
isAggregate (LCA.ArrayType _ _ _ _) = True
isAggregate _ = False

-- | Type which does not refer to other types
isLeafType :: TypePred
isLeafType (LCA.DirectType (LCA.TyComp _) _ _) = False
isLeafType (LCA.DirectType _ _ _) = True
isLeafType _ = False

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
