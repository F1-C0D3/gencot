{-# LANGUAGE PackageImports #-}
module Gencot.Items.Types where

import Control.Monad (liftM)
import System.FilePath (takeExtension,takeFileName,takeBaseName)

import Language.C.Data.Ident as LCI
import Language.C.Data.Node as LCN
import Language.C.Analysis as LCA

import Gencot.Items.Identifier (individualItemId,localItemId,paramItemId,typedefItemId,tagItemId,memberSubItemId,paramSubItemId,elemSubItemId,refSubItemId,resultSubItemId,indivItemIds,removePositions)
import Gencot.Names (srcFileName)
import Gencot.Traversal (FTrav,hasProperty)
import Gencot.Util.Types (getTagDef,isExtern,isFunction,resolveFully,TypeCarrier,TypeCarrierSet)

-- | Construct the identifier for an individual toplevel item.
-- An individual toplevel item is a function or a global object (variable).
-- It is specified by its declaration. 
-- The second argument is the source file name of @idec@.
getIndividualItemId :: LCA.IdentDecl -> String -> String
getIndividualItemId idec sfn = individualItemId (linkagePrefix idec sfn) (LCI.identToString $ LCA.declIdent idec)

-- | Construct the identifier for a individual non-internal toplevel item.
-- An individual non-internal toplevel item is a function or a global object (variable) with external linkage.
-- It is specified by its declaration. 
getExternalItemId :: LCA.IdentDecl -> String
getExternalItemId idec = individualItemId "" (LCI.identToString $ LCA.declIdent idec)

-- | The prefix to be prepended to an item identifier if the item has internal linkage.
-- The item is specified by its declaration. 
-- The second parameter is the source file name of @idec@.
linkagePrefix :: (LCA.Declaration d, LCN.CNode d) => d -> String -> String
linkagePrefix idec sfn | isInternal idec = prefix
    where prefix = if (takeExtension sfn) == ".c" then (takeBaseName sfn) else (takeFileName sfn)
          isInternal idec = 
            case LCA.declStorage idec of
                 NoStorage -> False -- function pointer struct members
                 _ -> LCA.declLinkage idec == LCA.InternalLinkage
linkagePrefix _ _ = ""

-- | Construct the identifier for an individual local item.
-- An individual local item is an object (variable) defined locally in a function body.
-- It is specified by its declaration. 
getLocalItemId :: LCA.IdentDecl -> String
getLocalItemId idec = localItemId (LCI.identToString $ LCA.declIdent idec)

-- | Construct the identifier for an individual parameter item.
-- An individual parameter item is a parameter defined locally in a function.
-- This is only intended as a dummy when directly translating a parameter declaration.
-- For production use @getParamSubItemId@ because that includes the function id.
getParamItemId :: LCA.ParamDecl -> String
getParamItemId idec = paramItemId (LCI.identToString $ LCA.declIdent idec)

-- | Construct the identifier for a collective item specified by a typedef name.
getTypedefItemId :: LCI.Ident -> String
getTypedefItemId idnam = typedefItemId (LCI.identToString idnam)

-- | Construct the identifier for a collective item specified by a compound tag name.
getTagItemId :: LCI.SUERef -> LCA.CompTyKind -> String
getTagItemId (LCI.AnonymousRef _) knd = tagItemId (kndstr knd) ""
getTagItemId (LCI.NamedRef idnam) knd = tagItemId (kndstr knd) (LCI.identToString idnam)

kndstr LCA.StructTag = "struct"
kndstr LCA.UnionTag = "union"

-- | Construct the identifier for a collective item specified by an enum tag name.
getEnumItemId :: LCI.SUERef -> String
getEnumItemId (LCI.AnonymousRef _) = tagItemId "enum" ""
getEnumItemId (LCI.NamedRef idnam) = tagItemId "enum" (LCI.identToString idnam)

-- | Get the identifier for a toplevel item which has not internal linkage
getToplevelItemId :: TypeCarrier -> String
getToplevelItemId (LCA.DeclEvent idecl) = getExternalItemId idecl
getToplevelItemId (LCA.TypeDefEvent (LCA.TypeDef idnam _ _ _)) = getTypedefItemId idnam
getToplevelItemId (LCA.TagEvent (LCA.CompDef (LCA.CompType sueref knd _ _ _))) = getTagItemId sueref knd
getToplevelItemId (LCA.TagEvent (LCA.EnumDef (LCA.EnumType sueref _ _ _))) = getEnumItemId sueref
getToplevelItemId (LCA.LocalEvent decl) = getLocalItemId decl
getToplevelItemId (LCA.ParamEvent decl) = getParamItemId decl
getToplevelItemId (LCA.AsmEvent _) = "<ASM block>"

-- | Construct the identifier for a member subitem of an item of struct or union type.
-- The first parameter is the identifier of the main item.
getMemberSubItemId :: String -> LCA.MemberDecl -> String
getMemberSubItemId item mdecl = memberSubItemId item (LCI.identToString $ LCA.declIdent mdecl)

-- | Construct the identifier for a parameter subitem of an item of function type.
-- The parameter is specified by the pair of its position and its declaration.
-- The first argument is the identifier of the main item.
getParamSubItemId :: String -> (Int,LCA.ParamDecl) -> String
getParamSubItemId item (pos,pdecl) = paramSubItemId item pos pnam
    where pnam = case LCA.declName pdecl of
                      LCA.VarName idnam _ -> (LCI.identToString idnam)
                      LCA.NoName -> ""

-- | Construct all identifiers for a collective item specified by a type.
-- Only supported for tag and typedef names and for pointer types where the ultimate base type is a tag or typedef name.
-- Several identifiers may result from resolving typed names or not.
derivedItemIds :: LCA.Type -> [String]
derivedItemIds (LCA.DirectType (LCA.TyComp (LCA.CompTypeRef sueref knd _)) _ _) | not $ LCI.isAnonymousRef sueref =
    [getTagItemId sueref knd]
derivedItemIds (LCA.DirectType (LCA.TyEnum (LCA.EnumTypeRef sueref _)) _ _) | not $ LCI.isAnonymousRef sueref =
    [getEnumItemId sueref]
derivedItemIds (LCA.TypeDefType (LCA.TypeDefRef idnam t _) _ _) = 
    (getTypedefItemId idnam) : (derivedItemIds t)
derivedItemIds (LCA.PtrType bt _ _) = 
    map (\s -> s ++ "*") $ derivedItemIds bt
derivedItemIds _ = []

-- | A type with an associated item identifier.
type ItemAssocType = (String,LCA.Type)

isNotNullItem :: ItemAssocType -> FTrav Bool
isNotNullItem (iid,t) = 
    liftM or $ mapM (hasProperty "nn") $ ((indivItemIds iid) ++ (derivedItemIds t))

isReadOnlyItem :: ItemAssocType -> FTrav Bool
isReadOnlyItem (iid,t) = 
    liftM or $ mapM (hasProperty "ro") $ ((indivItemIds iid) ++ (derivedItemIds t))

getIndividualItemAssoc :: LCA.IdentDecl -> String -> ItemAssocType
getIndividualItemAssoc idecl sfn = (getIndividualItemId idecl sfn, LCA.declType idecl)

getLocalItemAssoc :: LCA.IdentDecl -> ItemAssocType
getLocalItemAssoc idecl = (getLocalItemId idecl, LCA.declType idecl)

getParamItemAssoc :: LCA.ParamDecl -> ItemAssocType
getParamItemAssoc idecl = (getParamItemId idecl, LCA.declType idecl)

getTypedefItemAssoc :: LCI.Ident -> LCA.Type -> ItemAssocType
getTypedefItemAssoc idnam typ = (getTypedefItemId idnam, typ)

getMemberSubItemAssoc :: ItemAssocType -> LCA.MemberDecl -> ItemAssocType
getMemberSubItemAssoc (iid,_) mdecl = 
    (getMemberSubItemId iid mdecl, LCA.declType mdecl)

-- | Element sub-item  for ItemAssocType
-- The sub-ietm type must be explicitly provided as second argument as a hint to avoid resolving a typedef name.
getElemSubItemAssoc :: ItemAssocType -> LCA.Type -> ItemAssocType
getElemSubItemAssoc (iid,_) st = (elemSubItemId iid,st)

-- | Referenced data sub-item  for ItemAssocType
-- The sub-ietm type must be explicitly provided as second argument as a hint to avoid resolving a typedef name.
getRefSubItemAssoc :: ItemAssocType -> LCA.Type -> ItemAssocType
getRefSubItemAssoc (iid,_) st = (refSubItemId iid,st)

-- | Referenced data sub-item  for ItemAssocType
-- The sub-ietm type must be explicitly provided as second argument as a hint to avoid resolving a typedef name.
getResultSubItemAssoc :: ItemAssocType -> LCA.Type -> ItemAssocType
getResultSubItemAssoc (iid,_) st = (resultSubItemId iid,st)

-- | Parameter sub-item for ItemAssocType.
-- The parameter is specified by the pair of its position and its declaration.
-- Parameters of function type are adjusted to function pointer type.
-- Parameters of array type are not adjusted, since they are not treated as element pointers by Gencot.
getParamSubItemAssoc :: ItemAssocType -> (Int, LCA.ParamDecl) -> ItemAssocType
getParamSubItemAssoc (iid,_) ipd@(pos,pdecl) =
    if isFunction typ then adjustItemAssocType iat else iat
    where iat = (getParamSubItemId iid ipd, typ)
          typ = LCA.declType pdecl

-- | Adjust a type to a derived pointer type, together with its item identifier.
-- The item identifier is adjusted by prepending a "&".
adjustItemAssocType :: ItemAssocType -> ItemAssocType
adjustItemAssocType (iid,t) = ("&" ++ iid, (LCA.PtrType t LCA.noTypeQuals LCA.noAttributes))

-- | Retrieve ItemAssocType from a TypeCarrier.
-- The additional first parameter is a set of typedef names where to stop resolving external types.
-- This is a monadic action because the TypeCarrier's @srcFileName@ must be determined.
-- To avoid standalone parameters, local variables, and tagless compound items they must be filtered before.
-- AsmEvents must always be filtered.
-- External types are not resolved through anonymous composite types because that would require to 
-- modify the definition of the anonymous composite type in the symbol table.
getItemAssocType :: [String] -> TypeCarrier -> FTrav ItemAssocType
getItemAssocType _ (LCA.DeclEvent idecl) = do
    sfn <- srcFileName idecl
    return $ getIndividualItemAssoc idecl sfn
getItemAssocType tdn (LCA.TypeDefEvent td@(LCA.TypeDef idnam t _ _)) | isExtern td = 
    return $ getTypedefItemAssoc idnam $ resolveFully tdn t
getItemAssocType _ (LCA.TypeDefEvent (LCA.TypeDef idnam t _ _)) = 
    return $ getTypedefItemAssoc idnam t
getItemAssocType _ (LCA.TagEvent def@(LCA.CompDef (LCA.CompType sueref knd mems _ _))) =
    return (getTagItemId sueref knd,LCA.DirectType (LCA.typeOfTagDef def) LCA.noTypeQuals LCA.noAttributes)
getItemAssocType _ (LCA.TagEvent def@(LCA.EnumDef (LCA.EnumType sueref enms _ _))) =
    return (getEnumItemId sueref,LCA.DirectType (LCA.typeOfTagDef def) LCA.noTypeQuals LCA.noAttributes)
getItemAssocType _ (LCA.LocalEvent decl) = return $ getLocalItemAssoc decl
getItemAssocType _ (LCA.ParamEvent decl) = return $ getParamItemAssoc decl
getItemAssocType _ (LCA.AsmEvent _) = error "Cannot translate an ASM block as an item."

-- | Retrieve the ItemAssocTypes for the members of a compound tag definition.
-- This is a monadic action because it uses @getItemAssocType@.
getMemberItemAssocTypes :: TypeCarrier -> FTrav [ItemAssocType]
getMemberItemAssocTypes tc@(LCA.TagEvent def@(LCA.CompDef (LCA.CompType sueref knd mems _ _))) = do
    iat <- getItemAssocType [] tc
    return (map (\md -> getMemberSubItemAssoc iat md) mems)
getMemberItemAssocTypes _ = return []

-- | Get all sub-ItemAssocTypes of an ItemAssocType, including itself.
-- This is a monadic action because for an anonymous compound type the definition must be retrieved.
-- Paremeter sub-items of function type are adjusted to function pointer type.
getSubItemAssocTypes :: ItemAssocType -> FTrav [ItemAssocType]
getSubItemAssocTypes iat@(iid,(LCA.TypeDefType _ _ _)) = return [iat]
getSubItemAssocTypes iat@(iid,(LCA.DirectType (LCA.TyComp (LCA.CompTypeRef sueref knd _)) _ _)) | LCI.isAnonymousRef sueref = do
    dt <- LCA.getDefTable
    let mtd = getTagDef dt sueref
    case mtd of
         Nothing -> return []
         Just (LCA.CompDef (LCA.CompType _ _ mems _ _)) -> do
             subs <- liftM concat $ mapM (\md -> getSubItemAssocTypes $ getMemberSubItemAssoc iat md) mems
             return (iat : subs)
getSubItemAssocTypes iat@(iid,(LCA.DirectType _ _ _)) = return [iat] 
getSubItemAssocTypes iat@(iid,(LCA.PtrType bt _ _)) = do
    subs <- getSubItemAssocTypes $ getRefSubItemAssoc iat bt
    return (iat : subs)
getSubItemAssocTypes iat@(iid,(LCA.ArrayType bt _ _ _)) = do
    subs <- getSubItemAssocTypes $ getElemSubItemAssoc iat bt
    return (iat : subs)
getSubItemAssocTypes iat@(iid,(LCA.FunctionType (LCA.FunType rt pars _) _)) = do
    rsubs <- getSubItemAssocTypes $ getResultSubItemAssoc iat rt
    psubs <- mapM (\ipd -> getSubItemAssocTypes $ getParamSubItemAssoc iat ipd) $ numberList pars
    return (iat : (rsubs ++ (concat psubs)))
getSubItemAssocTypes iat@(iid,(LCA.FunctionType (LCA.FunTypeIncomplete rt) _)) = do
    subs <- getSubItemAssocTypes $ getResultSubItemAssoc iat rt
    return (iat : subs)

numberList :: [a] -> [(Int,a)]
numberList l = zip (iterate (1 +) 1) l 
