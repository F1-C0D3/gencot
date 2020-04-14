{-# LANGUAGE PackageImports #-}
module Gencot.Items.Types where

import Control.Monad (liftM)
import System.FilePath (takeExtension,takeFileName,takeBaseName)

import Language.C.Data.Ident as LCI
import Language.C.Data.Node as LCN
import Language.C.Analysis as LCA

import Gencot.Items.Identifier (individualItemId,localItemId,paramItemId,typedefItemId,tagItemId,memberSubItemId,paramSubItemId,elemSubItemId,refSubItemId,resultSubItemId,indivItemIds)
import Gencot.Names (srcFileName)
import Gencot.Traversal (FTrav,hasProperty,stopResolvTypeName)
import Gencot.Util.Types (getTagDef,isExtern,isFunction,isExternTypeDef,TypeCarrier,TypeCarrierSet,mergeQualsTo)

-- | Construct the identifier for an individual toplevel item.
-- An individual toplevel item is a function or a global object (variable).
-- It is specified by its declaration. 
-- The second argument is the source file name of the main file.
getIndividualItemId :: LCA.IdentDecl -> String -> String
getIndividualItemId idec sfn = individualItemId (linkagePrefix idec sfn) (LCI.identToString $ LCA.declIdent idec)

-- | Construct the identifier for a individual non-internal toplevel item.
-- An individual non-internal toplevel item is a function or a global object (variable) with external linkage.
-- It is specified by its declaration. 
getExternalItemId :: LCA.IdentDecl -> String
getExternalItemId idec = individualItemId "" (LCI.identToString $ LCA.declIdent idec)

-- | The prefix to be prepended to an item identifier if the item has internal linkage.
-- The item is specified by its declaration. 
-- The second parameter is the source file name of the main file.
linkagePrefix :: (LCA.Declaration d, LCN.CNode d) => d -> String -> String
linkagePrefix idec sfn | isInternal idec = prefix
    where fn = case LCN.fileOfNode idec of
                    Nothing -> "<unknown>"
                    Just res -> takeFileName res
          fn' = if fn == "<stdin>" then sfn else fn
          prefix = if (takeExtension fn') == ".c" then (takeBaseName fn') else fn'
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

-- | Get the item id of the (first) function subitem in an item.
-- The first argument is the type of the item, the second argument ist the item's id.
getFunctionSubItemId :: LCA.Type -> String -> String
getFunctionSubItemId (LCA.FunctionType _ _) baseid = baseid
getFunctionSubItemId (LCA.PtrType bt _ _) baseid = getFunctionSubItemId bt $ refSubItemId baseid
getFunctionSubItemId (LCA.ArrayType bt _ _ _) baseid = getFunctionSubItemId bt $ elemSubItemId baseid
getFunctionSubItemId (LCA.TypeDefType (LCA.TypeDefRef idnam typ _) _ _) _ = getFunctionSubItemId typ $ getTypedefItemId idnam
getFunctionSubItemId _ baseid = error ("getFunctionSubItemId for item with direct type: " ++ baseid)

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

isAddResultItem :: ItemAssocType -> FTrav Bool
isAddResultItem (iid,t) = 
    liftM or $ mapM (hasProperty "ar") $ ((indivItemIds iid) ++ (derivedItemIds t))

-- | ItemAssocType for an individual (top-level) item.
-- The second argument is the name of the main source file.
getIndividualItemAssoc :: LCA.IdentDecl -> String -> ItemAssocType
getIndividualItemAssoc idecl sfn = (getIndividualItemId idecl sfn, LCA.declType idecl)

-- | ItemAssocType for a local item (variable declared in a function).
getLocalItemAssoc :: LCA.IdentDecl -> ItemAssocType
getLocalItemAssoc idecl = (getLocalItemId idecl, LCA.declType idecl)

-- | ItemAssocType for a parameter (without known function).
getParamItemAssoc :: LCA.ParamDecl -> ItemAssocType
getParamItemAssoc idecl = (getParamItemId idecl, LCA.declType idecl)

-- | ItemAssocType for a named type.
getTypedefItemAssoc :: LCI.Ident -> LCA.Type -> ItemAssocType
getTypedefItemAssoc idnam typ = (getTypedefItemId idnam, typ)

-- | ItemAssocType for a composite type member.
-- The first argument is the ItemAssocType of the composite type.
getMemberSubItemAssoc :: ItemAssocType -> LCA.MemberDecl -> ItemAssocType
getMemberSubItemAssoc (iid,_) mdecl = 
    (getMemberSubItemId iid mdecl, LCA.declType mdecl)

-- | Element sub-item  for array ItemAssocType
getElemSubItemAssoc :: ItemAssocType -> FTrav ItemAssocType
getElemSubItemAssoc (iid,(LCA.ArrayType st _ _ _)) = hSubItemAssoc st (elemSubItemId iid)

-- | Referenced data sub-item for pointer ItemAssocType
getRefSubItemAssoc :: ItemAssocType -> FTrav ItemAssocType
getRefSubItemAssoc (iid,(LCA.PtrType st _ _)) = hSubItemAssoc st (refSubItemId iid)

-- | Result sub-item  for function ItemAssocType
getResultSubItemAssoc :: ItemAssocType -> FTrav ItemAssocType
getResultSubItemAssoc (iid,(LCA.FunctionType ft _)) = hSubItemAssoc (resultType ft) (resultSubItemId iid)
    where resultType (LCA.FunType t _ _) = t
          resultType (LCA.FunTypeIncomplete t) = t

-- | Return individual or collective ItemAssocType for the first argument.
-- If it is a typedef reference which is not resolved, use the corresponding collective Item id.
-- Otherwise use the second argument as item id.
hSubItemAssoc :: LCA.Type -> String -> FTrav ItemAssocType
hSubItemAssoc st@(LCA.TypeDefType (LCA.TypeDefRef idnam t _) _ _) iid = do
    rtn <- isResolvTypeName idnam
    return (if rtn then (iid,st) else (getTypedefItemAssoc idnam st))
hSubItemAssoc st iid = return (iid,st)

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
-- This is a monadic action because the TypeCarrier's @srcFileName@ must be determined.
-- To avoid standalone parameters, local variables, and tagless compound items they must be filtered before.
-- AsmEvents must always be filtered.
-- External types are not resolved through anonymous composite types because that would require to 
-- modify the definition of the anonymous composite type in the symbol table.
getItemAssocType :: TypeCarrier -> FTrav ItemAssocType
getItemAssocType (LCA.DeclEvent idecl) = do
    sfn <- srcFileName idecl
    return $ getIndividualItemAssoc idecl sfn
getItemAssocType (LCA.TypeDefEvent (LCA.TypeDef idnam t _ _)) = 
    return $ getTypedefItemAssoc idnam t
getItemAssocType (LCA.TagEvent def@(LCA.CompDef (LCA.CompType sueref knd mems _ _))) =
    return (getTagItemId sueref knd,LCA.DirectType (LCA.typeOfTagDef def) LCA.noTypeQuals LCA.noAttributes)
getItemAssocType (LCA.TagEvent def@(LCA.EnumDef (LCA.EnumType sueref enms _ _))) =
    return (getEnumItemId sueref,LCA.DirectType (LCA.typeOfTagDef def) LCA.noTypeQuals LCA.noAttributes)
getItemAssocType (LCA.LocalEvent decl) = return $ getLocalItemAssoc decl
getItemAssocType (LCA.ParamEvent decl) = return $ getParamItemAssoc decl
getItemAssocType (LCA.AsmEvent _) = error "Cannot translate an ASM block as an item."

-- | Retrieve the ItemAssocTypes for the members of a compound tag definition.
-- This is a monadic action because it uses @getItemAssocType@.
getMemberItemAssocTypes :: TypeCarrier -> FTrav [ItemAssocType]
getMemberItemAssocTypes tc@(LCA.TagEvent def@(LCA.CompDef (LCA.CompType sueref knd mems _ _))) = do
    iat <- getItemAssocType tc
    return (map (\md -> getMemberSubItemAssoc iat md) mems)
getMemberItemAssocTypes _ = return []

-- | Get all sub-ItemAssocTypes of an ItemAssocType, including itself.
-- This is a monadic action because for an anonymous compound type the definition must be retrieved
-- and type names must be tested whether they stop resolving.
-- Paremeter sub-items of function type are adjusted to function pointer type.
getSubItemAssocTypes :: ItemAssocType -> FTrav [ItemAssocType]
getSubItemAssocTypes iat@(iid,(LCA.TypeDefType (LCA.TypeDefRef idnam t _) q _)) = do
    dt <- LCA.getDefTable
    srtn <- stopResolvTypeName idnam
    if ((isExternTypeDef dt idnam) && not srtn)
       then getSubItemAssocTypes (iid,(mergeQualsTo t q))
       else return [iat]
getSubItemAssocTypes iat@(iid,(LCA.DirectType (LCA.TyComp (LCA.CompTypeRef sueref knd _)) _ _)) | LCI.isAnonymousRef sueref = do
    dt <- LCA.getDefTable
    let mtd = getTagDef dt sueref
    case mtd of
         Nothing -> return []
         Just (LCA.CompDef (LCA.CompType _ _ mems _ _)) -> do
             subs <- liftM concat $ mapM (\md -> getSubItemAssocTypes $ getMemberSubItemAssoc iat md) mems
             return (iat : subs)
getSubItemAssocTypes iat@(iid,(LCA.DirectType _ _ _)) = return [iat] 
getSubItemAssocTypes iat@(iid,(LCA.PtrType _ _ _)) = do
    sub <- getRefSubItemAssoc iat
    subs <- getSubItemAssocTypes sub
    return (iat : subs)
getSubItemAssocTypes iat@(iid,(LCA.ArrayType _ _ _ _)) = do
    sub <- getElemSubItemAssoc iat
    subs <- getSubItemAssocTypes sub
    return (iat : subs)
getSubItemAssocTypes iat@(iid,(LCA.FunctionType (LCA.FunType rt pars _) _)) = do
    sub <- getResultSubItemAssoc iat
    rsubs <- getSubItemAssocTypes sub
    psubs <- mapM (\ipd -> getSubItemAssocTypes $ getParamSubItemAssoc iat ipd) $ numberList pars
    return (iat : (rsubs ++ (concat psubs)))
getSubItemAssocTypes iat@(iid,(LCA.FunctionType (LCA.FunTypeIncomplete rt) _)) = do
    sub <- getResultSubItemAssoc iat
    subs <- getSubItemAssocTypes sub
    return (iat : subs)

numberList :: [a] -> [(Int,a)]
numberList l = zip (iterate (1 +) 1) l 

isResolvTypeName :: Ident -> FTrav Bool
isResolvTypeName idnam = do
    dt <- getDefTable
    srtn <- stopResolvTypeName idnam
    return ((isExternTypeDef dt idnam) && not srtn)
