{-# LANGUAGE PackageImports, TypeSynonymInstances, FlexibleInstances #-}
module Gencot.Util.Types where

import Data.Maybe (catMaybes)
import Data.List (nub,(\\),isPrefixOf,union,elem)
import Data.Foldable (find)

import Language.C.Analysis as LCA
import Language.C.Data.Ident as LCI
import qualified Language.C.Analysis.DefTable as LCD
import Language.C.Data.Node as LCN
import Language.C.Analysis.TravMonad (Trav,MonadSymtab)

import Gencot.Util.Equality

type TypeCarrier = LCA.DeclEvent
type TypeCarrierSet = [TypeCarrier]

-- | Callback handler for collecting initial type carriers
collectTypeCarriers :: TypeCarrier -> Trav TypeCarrierSet ()
collectTypeCarriers e@(LCA.DeclEvent (LCA.ObjectDef _)) | carriesNonPrimitive e = modifyUserState (e:)
collectTypeCarriers e@(LCA.DeclEvent (LCA.FunctionDef _)) | carriesNonPrimitive e = modifyUserState (e:)
collectTypeCarriers e@(LCA.LocalEvent _) | carriesNonPrimitive e = modifyUserState (e:)
collectTypeCarriers e@(LCA.TypeDefEvent _) 
    | carriesNonPrimitive e && (not . isExtern) e = modifyUserState (e:)
collectTypeCarriers e@(LCA.TagEvent (LCA.CompDef _)) 
    | carriesNonPrimitive e && (not . isExtern) e = modifyUserState (e:)
collectTypeCarriers _ = return ()

carriesNonPrimitive :: TypeCarrier -> Bool
carriesNonPrimitive = not . (all isPrimitive) . carriedTypes

carriedTypes :: TypeCarrier -> TypeSet
carriedTypes (LCA.DeclEvent decl@(LCA.FunctionDef _)) = selInFunction (const True) $ LCA.declType decl
carriedTypes (LCA.DeclEvent decl) | isFunction $ LCA.declType decl = selInFunction (const True) $ LCA.declType decl
carriedTypes (LCA.DeclEvent decl) = [LCA.declType decl]
carriedTypes (LCA.LocalEvent decl) = [LCA.declType decl]
carriedTypes (LCA.ParamEvent decl) = [LCA.declType decl]
carriedTypes (LCA.TypeDefEvent (LCA.TypeDef _ t _ _)) = [t]
carriedTypes (LCA.TagEvent (LCA.CompDef (LCA.CompType _ _ mems _ _))) = nub $ map LCA.declType mems
carriedTypes _ = []

transCloseUsedCarriers :: LCD.DefTable -> TypeCarrierSet -> TypeCarrierSet
transCloseUsedCarriers dt tcs = transCloseCarriers (usedCarriers (usedTypeNames tcs) dt) tcs

-- | The typedef names used (referenced) in a set of type carriers.
-- Get the carried types, 
-- get their non-derived contained types which are typedef references, 
-- and return their typedef names.
usedTypeNames :: TypeCarrierSet -> [String]
usedTypeNames tcs = map (LCI.identToString . typeIdent) $ nub $ concat $ map (selNonDerived isTypeDefRef) $ concat $ map carriedTypes tcs

-- | Typedef names of external type definitions.
externTypeNames :: TypeCarrierSet -> [String]
externTypeNames tcs = catMaybes $ map getDefinedTypeName (filter isExtern tcs)

getDefinedTypeName :: LCA.DeclEvent -> Maybe String
getDefinedTypeName (LCA.TypeDefEvent (LCA.TypeDef idnam _ _ _)) = Just $ LCI.identToString idnam
getDefinedTypeName _ = Nothing

-- | Transitive closure of a function on type carriers, applied to a set of type carriers
transCloseCarriers :: (TypeCarrier -> TypeCarrierSet) -> TypeCarrierSet -> TypeCarrierSet
transCloseCarriers f tcs = 
    if null (ct \\ tcs) then tcs else transCloseCarriers f ct
    where ct = nub $ concat $ map f tcs

-- | The set of type carriers referenced via types from a given type carrier.
-- If the given type carrier is a tag or typedef it is included in the result.
usedCarriers :: [String] -> LCD.DefTable -> TypeCarrier -> TypeCarrierSet
usedCarriers tds dt tc = nub ((selfCarrierType tc) ++ (concat $ map (usedCarriersInType (isExtern tc) tds dt) $ carriedTypes tc))

selfCarrierType :: TypeCarrier -> TypeCarrierSet
selfCarrierType tc@(LCA.TypeDefEvent _) = [tc]
selfCarrierType tc@(LCA.TagEvent _) = [tc]
selfCarrierType _ = []

-- | Get carriers (tag and type defs) used in a type
-- If first parameter is true, fully resolve used type defs
-- The second parameter is a list of type defs names where resolving stops
usedCarriersInType :: Bool -> [String] -> LCD.DefTable -> LCA.Type -> TypeCarrierSet
usedCarriersInType rslv tds dt t = 
    catMaybes $ map (typeToCarrier dt) $ selNonDerived isTypeCarrier rt
    where rt = if rslv then resolveFully tds t else t

isTypeCarrier :: LCA.Type -> Bool
isTypeCarrier (LCA.DirectType (LCA.TyComp _) _ _) = True
isTypeCarrier (LCA.DirectType (LCA.TyEnum _) _ _) = True
isTypeCarrier (LCA.TypeDefType _ _ _) = True
isTypeCarrier _ = False

typeToCarrier :: LCD.DefTable -> LCA.Type -> Maybe TypeCarrier
typeToCarrier dt (LCA.DirectType (LCA.TyComp (LCA.CompTypeRef ref _ _)) _ _) = getTagDefEvent dt ref
typeToCarrier dt (LCA.DirectType (LCA.TyEnum (LCA.EnumTypeRef ref _)) _ _) = getTagDefEvent dt ref
typeToCarrier dt (LCA.TypeDefType (LCA.TypeDefRef nam _ _) _ _) = getTypeDefEvent dt nam
typeToCarrier _ _ = Nothing

getTagDefEvent :: LCD.DefTable -> LCI.SUERef -> Maybe TypeCarrier
getTagDefEvent dt ref = fmap LCA.TagEvent $ getTagDef dt ref

getTypeDefEvent :: LCD.DefTable -> LCI.Ident -> Maybe TypeCarrier
getTypeDefEvent dt nam = fmap LCA.TypeDefEvent $ getTypeDef dt nam

resolveSetFully :: Bool -> [String] -> TypeSet -> TypeSet
resolveSetFully False _ ts = ts
resolveSetFully True tds ts = map (resolveFully tds) ts

resolveFully :: [String] -> LCA.Type -> LCA.Type
resolveFully tds (LCA.TypeDefType (LCA.TypeDefRef nam t _) _ _) = 
    if elem (LCI.identToString nam) tds then t else resolveFully tds t
resolveFully tds (LCA.PtrType t q n) = LCA.PtrType (resolveFully tds t) q n
resolveFully tds (LCA.ArrayType t i q n) = LCA.ArrayType (resolveFully tds t) i q n
resolveFully tds (LCA.FunctionType (LCA.FunType rt pars v) n) = 
    LCA.FunctionType (LCA.FunType (resolveFully tds rt) (map (resolveFullyInParDecl tds) pars) v) n
resolveFully tds (LCA.FunctionType (LCA.FunTypeIncomplete rt) n) = 
    LCA.FunctionType (LCA.FunTypeIncomplete (resolveFully tds rt)) n
resolveFully tds t = t

resolveFullyInParDecl tds (LCA.ParamDecl (LCA.VarDecl vn a t) n) = 
    LCA.ParamDecl (LCA.VarDecl vn a (resolveFully tds t)) n
resolveFullyInParDecl tds (LCA.AbstractParamDecl (LCA.VarDecl vn a t) n) = 
    LCA.AbstractParamDecl (LCA.VarDecl vn a (resolveFully tds t)) n

carrierInTable :: LCD.DefTable -> TypeCarrier -> Bool
carrierInTable dt (LCA.DeclEvent decl) = maybe False (decl ==) $ getDeclaration dt (LCA.declIdent decl)
carrierInTable dt (LCA.TypeDefEvent tdef) = maybe False (tdef ==) $ getTypeDef dt (LCA.identOfTypeDef tdef)
carrierInTable dt (LCA.TagEvent tdef) = maybe False (tdef ==) $ getTagDef dt (LCA.sueRef tdef)

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

-- | Transitive closure with all base and parameter types of derived types
-- all fully resolved external typedefs
-- and all member types of external composite types.
closeDerivedAndExternal :: LCD.DefTable -> TypeSet -> TypeSet
closeDerivedAndExternal dt types = transCloseTypes (selTypes (not . isPrimitive)) types
    where selTypes p = unionTypeSelector [selInDerived p, selInFunction p, selInExtTypeDef dt p, selInExtComp dt p]

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

-- | Type selector which fully resolves external type definition, with additional result filter.
-- Needs a symbol table to look up the type definitions
selInExtTypeDef :: LCD.DefTable -> TypePred -> TypeSelector
selInExtTypeDef dt flt (LCA.TypeDefType (LCA.TypeDefRef ident t _) _ _) | isExternTypeDef dt ident =
    considerType flt $ resolveTypedef t
selInExtTypeDef _ _ _ = []

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
    case getTagDef dt ref of
         Nothing -> []
         Just (LCA.CompDef (LCA.CompType _ _ mems _ _)) ->
            nub $ concat $ map (declTypes flt) mems
selInComp _ _ _ = []

-- | Type selector for the member types of external composite types, with additional result filter.
-- Needs a symbol table to look up the tag definitions.
selInExtComp :: LCD.DefTable -> TypePred -> TypeSelector
selInExtComp dt flt typ@(LCA.DirectType (LCA.TyComp (LCA.CompTypeRef ref _ _)) _ _) | isExternComp dt ref =
    selInComp dt flt typ
selInExtComp _ _ _ = []

-- | Type selector for all types referenced in the given types, with additional result filter.
selInAllTypes :: LCD.DefTable -> TypePred -> TypeSelector
selInAllTypes dt p = unionTypeSelector [selInTypeDef p,selInDerived p,selInFunction p,selInComp dt p]

-- | Type selector for all types directly contained in the given type, with additional result filter.
selInContained :: TypePred -> TypeSelector
selInContained p = unionTypeSelector [selInDerived p,selInFunction p]

-- | Type selector for all non-derived types directly contained in the given type, with additional result filter.
selNonDerived :: TypePred -> TypeSelector
selNonDerived p (LCA.PtrType t _ _) = selNonDerived p t
selNonDerived p (LCA.ArrayType t _ _ _) = selNonDerived p t
selNonDerived p (LCA.FunctionType (LCA.FunType rt pars _) _) = 
    union (selNonDerived p rt) (nub $ concat $ map ((selNonDerived p) . LCA.declType) pars)
selNonDerived p (LCA.FunctionType (LCA.FunTypeIncomplete rt) _) = selNonDerived p rt
selNonDerived p t = considerType p t

-- | Get derived types occurring syntactically in a type, including the type itself.
-- All result types are paired with an item id. The first argument is an item id for the type itself.
{-
getDerivedParts :: String -> LCA.Type -> [(String,LCA.Type)]
getDerivedParts iid t@(LCA.PtrType bt _ _) = (iid,t) : getDerivedParts (getRefSubItemId iid) bt
getDerivedParts iid t@(LCA.ArrayType bt _ _ _) = (iid,t) : getDerivedParts (getElemSubItemId iid) bt
getDerivedParts iid t@(LCA.FunctionType (LCA.FunType rt pars _) _) = 
    (iid,t) : union (getDerivedParts (getResultSubItemId iid) rt) 
                    (nub $ concat $ map (\p -> getDerivedParts (getParamSubItemId iid p) $ LCA.declType p) pars)
getDerivedParts iid t@(LCA.FunctionType (LCA.FunTypeIncomplete rt) _) = (iid,t) : getDerivedParts (getResultSubItemId iid) rt
getDerivedParts _ _ = []
-}

isLinearType :: MonadSymtab m => LCA.Type -> m Bool
isLinearType td@(LCA.TypeDefType _ _ _) = isLinearType $ resolveTypedef td
isLinearType (LCA.PtrType t _ _) = return $ not $ isFunction t
isLinearType (LCA.ArrayType t _ _ _) = isLinearType t
isLinearType (LCA.DirectType (LCA.TyComp (LCA.CompTypeRef sueref _ _)) _ _) = do
    table <- LCA.getDefTable
    case getTagDef table sueref of
         Nothing -> return False
         Just (LCA.CompDef (LCA.CompType _ _ mdecls _ _)) -> do
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
isReadOnlyType (LCA.ArrayType t _ _ _) =
    if isConstQualified t 
       then isReadOnlyType t
       else return False
isReadOnlyType (LCA.FunctionType _ _) = return True
isReadOnlyType (LCA.DirectType (LCA.TyComp (LCA.CompTypeRef sueref _ _)) _ _) = do
    table <- LCA.getDefTable
    case getTagDef table sueref of
         Nothing -> return False
         Just (LCA.CompDef (LCA.CompType _ _ mdecls _ _)) -> do
             h <- mapM (isReadOnlyType . LCA.declType) mdecls
             return $ all id h
isReadOnlyType (LCA.DirectType _ _ _) = return True

isReadOnlyParType :: MonadSymtab m => LCA.Type -> m Bool
isReadOnlyParType arr@(LCA.ArrayType t _ _ _) = 
    if isFunction t 
       then return True
       else isReadOnlyType arr
isReadOnlyParType t = isReadOnlyType t

isConstQualified :: TypePred
isConstQualified (LCA.TypeDefType (LCA.TypeDefRef _ t _) tq _) = constant tq || isConstQualified t
isConstQualified (LCA.PtrType _ tq _) = constant tq
isConstQualified (LCA.ArrayType _ _ tq _) = constant tq
isConstQualified (LCA.FunctionType _ _) = False
isConstQualified (LCA.DirectType _ tq _) = constant tq

isExternTypeDef :: LCD.DefTable -> LCI.Ident -> Bool
isExternTypeDef dt ident = 
    case LCD.lookupIdent ident dt of
         Nothing -> False
         Just (Right _) -> False
         Just (Left typeDef) -> isExtern typeDef

isExternComp :: LCD.DefTable -> LCI.SUERef -> Bool
isExternComp dt ref =
    case LCD.lookupTag ref dt of
         Nothing -> False
         Just (Left _) -> False
         Just (Right tagDef) -> isExtern tagDef

-- | Heuristics: a node is considered extern if the file name is absolute.
-- This is usually the case for all system includes.
isExtern :: CNode n => n -> Bool
isExtern n = case LCN.fileOfNode n of
                  Nothing -> False
                  Just fpath -> "/" `isPrefixOf` fpath

isCompOrFunc :: TypePred
isCompOrFunc td@(LCA.TypeDefType _ _ _) = isCompOrFunc $ resolveTypedef td
isCompOrFunc (LCA.DirectType (LCA.TyComp _) _ _) = True
isCompOrFunc (LCA.FunctionType _ _) = True
isCompOrFunc _ = False

isNamedFunPointer :: TypePred
isNamedFunPointer (LCA.PtrType t _ _) = isTypeDefRef t && isFunction t
isNamedFunPointer _ = False

getsParmodDescr :: TypePred
getsParmodDescr (LCA.FunctionType _ _) = True
getsParmodDescr (LCA.PtrType (LCA.FunctionType _ _) _ _) = True
getsParmodDescr (LCA.ArrayType t _ _ _) = getsParmodDescr t
getsParmodDescr _ = False

isFunPointerOptArr :: TypePred
isFunPointerOptArr td@(LCA.TypeDefType _ _ _) = isFunPointerOptArr $ resolveTypedef td
isFunPointerOptArr (LCA.ArrayType t _ _ _) = isFunPointerOptArr t
isFunPointerOptArr t = isFunPointer t

isFunPointer :: TypePred
isFunPointer td@(LCA.TypeDefType _ _ _) = isFunPointer $ resolveTypedef td
isFunPointer (LCA.PtrType t _ _) = isFunction t
isFunPointer _ = False

isFunction :: TypePred
isFunction td@(LCA.TypeDefType _ _ _) = isFunction $ resolveTypedef td
isFunction (LCA.FunctionType _ _) = True
isFunction _ = False

isComplete :: TypePred
isComplete td@(LCA.TypeDefType _ _ _) = isComplete $ resolveTypedef td
isComplete (LCA.FunctionType (LCA.FunTypeIncomplete _) _) = False
isComplete _ = True

isPointer :: TypePred
isPointer td@(LCA.TypeDefType _ _ _) = isPointer $ resolveTypedef td
isPointer (LCA.PtrType _ _ _) = True
isPointer _ = False

isArray :: TypePred
isArray td@(LCA.TypeDefType _ _ _) = isArray $ resolveTypedef td
isArray (LCA.ArrayType _ _ _ _) = True
isArray _ = False

isComposite :: TypePred
isComposite td@(LCA.TypeDefType _ _ _) = isComposite $ resolveTypedef td
isComposite (LCA.DirectType (LCA.TyComp _) _ _) = True
isComposite _ = False

isAggregate :: TypePred
isAggregate td@(LCA.TypeDefType _ _ _) = isAggregate $ resolveTypedef td
isAggregate (LCA.DirectType (LCA.TyComp _) _ _) = True
isAggregate (LCA.ArrayType _ _ _ _) = True
isAggregate _ = False

isVoid :: TypePred
isVoid td@(LCA.TypeDefType _ _ _) = isVoid $ resolveTypedef td
isVoid (LCA.DirectType LCA.TyVoid _ _) = True
isVoid _ = False

isAggPointer :: TypePred
isAggPointer (LCA.PtrType t _ _) = isAggregate t
isAggPointer _ = False

isCompPointer :: TypePred
isCompPointer (LCA.PtrType t _ _) = isComposite t
isCompPointer _ = False

-- | Type which does not refer to other types
isLeafType :: TypePred
isLeafType (LCA.DirectType (LCA.TyComp _) _ _) = False
isLeafType (LCA.DirectType _ _ _) = True
isLeafType _ = False

isPrimitive :: TypePred
isPrimitive (LCA.DirectType (LCA.TyEnum _) _ _) = False
isPrimitive t = isLeafType t

isTagRef :: TypePred
isTagRef (LCA.DirectType (LCA.TyEnum _) _ _) = True
isTagRef (LCA.DirectType (LCA.TyComp _) _ _) = True
isTagRef _ = False

isTypeDefRef :: TypePred
isTypeDefRef (LCA.TypeDefType _ _ _) = True
isTypeDefRef _ = False

isDerivedType :: TypePred
isDerivedType (LCA.PtrType _ _ _) = True
isDerivedType (LCA.ArrayType _ _ _ _) = True
isDerivedType (LCA.FunctionType _ _) = True
isDerivedType _ = False

containsTypedefs :: TypePred
containsTypedefs (LCA.TypeDefType _ _ _) = True
containsTypedefs (LCA.DirectType _ _ _) = False
containsTypedefs (LCA.PtrType t _ _) = containsTypedefs t
containsTypedefs (LCA.ArrayType t _ _ _) = containsTypedefs t
containsTypedefs (LCA.FunctionType (LCA.FunTypeIncomplete t) _) = containsTypedefs t
containsTypedefs (LCA.FunctionType (LCA.FunType rt pars _) _) = 
    (containsTypedefs rt) || any (\pd -> containsTypedefs $ LCA.declType pd) pars

resolveTypedef :: LCA.Type -> LCA.Type
resolveTypedef (LCA.TypeDefType (LCA.TypeDefRef _ t _) _ _) = resolveTypedef t
resolveTypedef t = t

getParmodFunctionType :: LCA.Type -> LCA.Type
getParmodFunctionType t | isFunPointerOptArr t = getPointedType t
getParmodFunctionType t | isFunction t = t
getParmodFunctionType _ = error "No function (pointer (array)) type passed to getParmodFunctionType"

getDeclaration :: LCD.DefTable -> LCI.Ident -> Maybe LCA.IdentDecl
getDeclaration dt nam =
    case LCD.lookupIdent nam dt of
         Nothing -> Nothing
         Just (Left _) -> Nothing
         Just (Right decl) -> Just decl

getTagDef :: LCD.DefTable -> LCI.SUERef -> Maybe LCA.TagDef
getTagDef dt ref =
    case LCD.lookupTag ref dt of
         Nothing -> Nothing
         Just (Left _) -> Nothing
         Just (Right tagDef) -> Just tagDef

getTypeDef :: LCD.DefTable -> LCI.Ident -> Maybe LCA.TypeDef
getTypeDef dt nam = 
    case LCD.lookupIdent nam dt of
         Nothing -> Nothing
         Just (Right _) -> Nothing
         Just (Left typeDef) -> Just typeDef
         
getPointedType :: LCA.Type -> LCA.Type
getPointedType t | isPointer t = rt
    where (LCA.PtrType rt _ _) = resolveTypedef t
getPointedType t | isArray t = getPointedType rt
    where (LCA.ArrayType rt _ _ _) = resolveTypedef t
getPointedType _ = error "No pointer (array) type passed to getPointedType"

-- | Adjust a function type as function pointer type, together with its item identifier.
-- The item identifier is adjusted by prepending a "&".
wrapFunAsPointer :: (String,LCA.Type) -> (String,LCA.Type)
wrapFunAsPointer (iid,t@(LCA.FunctionType _ _)) = ("&" ++ iid, (LCA.PtrType t LCA.noTypeQuals []))
wrapFunAsPointer t = t

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

typeIdent (LCA.TypeDefType (LCA.TypeDefRef ident _ _) _ _) = ident
