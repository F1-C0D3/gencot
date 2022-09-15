{-# LANGUAGE PackageImports #-}
module Gencot.Items.Types where

import Control.Monad (liftM)
import System.FilePath (takeExtension,takeFileName,takeBaseName)
import Data.List (isPrefixOf,find,sort)
import Data.Maybe (fromMaybe)

import Language.C.Data.Ident as LCI
import Language.C.Data.Node as LCN
import Language.C.Analysis as LCA

import Gencot.Items.Identifier (individualItemId,localItemId,paramItemId,typedefItemId,tagItemId,memberSubItemId,paramSubItemId,elemSubItemId,refSubItemId,resultSubItemId,indivItemIds,getParamName)
import Gencot.Names (getFileName,anonCompTypeName,srcFileName)
import Gencot.Traversal (FTrav,hasProperty,stopResolvTypeName,getItems,getProperties,getFunDef)
import Gencot.Util.Types (getTagDef,isExtern,isFunction,isExternTypeDef,TypeCarrier,TypeCarrierSet,mergeQualsTo,safeDeclLinkage)

-- | Construct the identifier for an individual toplevel item.
-- An individual toplevel item is a function or a global object (variable).
-- It is specified by its declaration. 
-- The second argument is the source file name of the main file.
getIndividualItemId :: LCA.IdentDecl -> String -> String
getIndividualItemId idec sfn = individualItemId (linkagePrefix idec sfn) (LCI.identToString $ LCA.declIdent idec)

-- | The prefix to be prepended to an item identifier if the item has internal linkage.
-- The item is specified by its declaration. 
-- The second parameter is the source file name of the main file.
linkagePrefix :: (LCA.Declaration d, LCN.CNode d) => d -> String -> String
linkagePrefix idec sfn | isInternal idec = prefix
    where fn = srcFileName sfn idec
          prefix = if (takeExtension fn) == ".c" then (takeBaseName fn) else fn
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

-- | Construct the identifier for a collective item specified by a compound type.
-- The second argument is the name of the main source file.
-- It may be used for constructing the item id in case of a tagless type.
getTagItemId :: LCA.CompType -> String -> String
getTagItemId (LCA.CompType (LCI.AnonymousRef _) knd _ _ n) sfn = tagItemId (kndstr knd) $ anonCompTypeName sfn n
getTagItemId (LCA.CompType (LCI.NamedRef idnam) knd _ _ _) _ = tagItemId (kndstr knd) $ LCI.identToString idnam

kndstr LCA.StructTag = "struct"
kndstr LCA.UnionTag = "union"

-- | Construct the identifier for a collective item specified by an enum tag name.
getEnumItemId :: LCI.SUERef -> String
getEnumItemId (LCI.AnonymousRef _) = tagItemId "enum" ""
getEnumItemId (LCI.NamedRef idnam) = tagItemId "enum" (LCI.identToString idnam)

-- | Get the identifier for an external toplevel item
-- Since the item is external, the main file name is not required:
-- The linkage prefix is only required for items with internal linkage.
-- If a tagless type is defined in the main file it is not external.
getToplevelItemId :: TypeCarrier -> String
getToplevelItemId (LCA.DeclEvent idecl) = individualItemId "" (LCI.identToString $ LCA.declIdent idecl)
getToplevelItemId (LCA.TypeDefEvent (LCA.TypeDef idnam _ _ _)) = getTypedefItemId idnam
getToplevelItemId (LCA.TagEvent (LCA.CompDef ct)) = getTagItemId ct ""
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
derivedItemIds :: LCA.Type -> FTrav [String]
derivedItemIds (LCA.DirectType (LCA.TyComp (LCA.CompTypeRef sueref _ _)) _ _) = do
    dt <- LCA.getDefTable
    sfn <- getFileName
    case getTagDef dt sueref of
         Nothing -> return []
         Just (LCA.CompDef ct) -> return [getTagItemId ct sfn]
derivedItemIds (LCA.DirectType (LCA.TyEnum (LCA.EnumTypeRef sueref _)) _ _) | not $ LCI.isAnonymousRef sueref =
    return $ [getEnumItemId sueref]
derivedItemIds (LCA.TypeDefType (LCA.TypeDefRef idnam t _) _ _) = do
    dii <- derivedItemIds t
    return $ (getTypedefItemId idnam) : dii
derivedItemIds (LCA.PtrType bt _ _) = do
    dii <- derivedItemIds bt
    return $ map (\s -> s ++ "*") dii
derivedItemIds _ = return $ []

-- | A type with an associated item identifier.
type ItemAssocType = (String,LCA.Type)

isItemWithProperty :: String -> ItemAssocType -> FTrav Bool
isItemWithProperty p (iid,t) = do
    dii <- derivedItemIds t
    liftM or $ mapM (hasProperty p) $ ((indivItemIds iid) ++ dii)

isNotNullItem = isItemWithProperty "nn"
isReadOnlyItem = isItemWithProperty "ro"
isAddResultItem = isItemWithProperty "ar"
isNoStringItem = isItemWithProperty "ns"

-- | The AddResult property is suppressed by a ReadOnly property.
shallAddResult :: ItemAssocType -> FTrav Bool
shallAddResult iat = do
    ar <- isAddResultItem iat
    ro <- isReadOnlyItem iat
    return (ar && (not ro))

-- | Retrieve all subitems with a gs property.
-- This includes virtual parameter items not declared for the C function.
getGlobalStateSubItemIds :: ItemAssocType -> FTrav [String]
getGlobalStateSubItemIds (fid,_) = 
    getItems (\iid plist -> (fidslash `isPrefixOf` iid) && any (\p -> "gs" `isPrefixOf` p) plist)
    where fidslash = fid ++ "/"

-- | Get the Global-State property for an item.
-- If not present return the empty string.
getGlobalStateProperty :: String -> FTrav String
getGlobalStateProperty iid = do
    props <- getProperties iid
    return $ fromMaybe "" $ find (\p -> "gs" `isPrefixOf` p) props

-- | Retrieve the item identifier of the toplevel item with the given gs property.
-- If there is more than one, an arbitrary one is returned. 
-- If there is none, the empty string is returned.
getGlobalStateId :: String -> FTrav String
getGlobalStateId gs = do
    ids <- getItems (\iid plist -> (all (\c -> c /= '/' && c /= '.' && c /= '|') iid) && (elem gs plist))
    return (if null ids then "" else head ids)

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

-- | ItemAssocType for an compound type item.
-- The second argument is the name of the main source file.
getTagItemAssoc :: LCA.TagDef -> String -> ItemAssocType
getTagItemAssoc def@(LCA.CompDef ct) sfn = (getTagItemId ct sfn,LCA.DirectType (LCA.typeOfTagDef def) LCA.noTypeQuals LCA.noAttributes)

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

-- | Construct item assoc types for all parameters to be added by a Global-State property.
-- The argument is the item associated type of the function. 
-- The item names are taken from the declarations of the virtual items.
-- As type the type void is used as a dummy, we only need the item associatd type to access its properties.
makeGlobalStateItemAssocTypes :: ItemAssocType -> FTrav [ItemAssocType]
makeGlobalStateItemAssocTypes fiat = do
    gsids <- getGlobalStateSubItemIds fiat
    return $ map (\iid -> (iid, LCA.DirectType LCA.TyVoid LCA.noTypeQuals LCA.noAttributes)) gsids

-- | Adjust a type to a derived pointer type, together with its item identifier.
-- The item identifier is adjusted by prepending a "&".
adjustItemAssocType :: ItemAssocType -> ItemAssocType
adjustItemAssocType (iid,t) = ("&" ++ iid, (LCA.PtrType t LCA.noTypeQuals LCA.noAttributes))

-- | Retrieve ItemAssocType from a TypeCarrier.
-- This is a monadic action because the @getFileName@ must be determined.
-- To avoid standalone parameters, local variables, and tagless compound items they must be filtered before.
-- AsmEvents must always be filtered.
-- External types are never resolved, if they are not stopResolve they must be filtered before.
getItemAssocType :: TypeCarrier -> FTrav ItemAssocType
getItemAssocType (LCA.DeclEvent idecl) = do
    sfn <- getFileName
    return $ getIndividualItemAssoc idecl sfn
getItemAssocType (LCA.TypeDefEvent (LCA.TypeDef idnam t _ _)) = 
    return $ getTypedefItemAssoc idnam t
getItemAssocType (LCA.TagEvent def@(LCA.CompDef ct)) = do
    sfn <- getFileName
    return $ getTagItemAssoc def sfn
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
-- This is a monadic action because type names must be tested whether they stop resolving.
-- Paremeter sub-items of function type are adjusted to function pointer type.
getSubItemAssocTypes :: ItemAssocType -> FTrav [ItemAssocType]
getSubItemAssocTypes iat@(iid,(LCA.TypeDefType (LCA.TypeDefRef idnam t _) q _)) = do
    rtn <- isResolvTypeName idnam
    if rtn
       then getSubItemAssocTypes (iid,(mergeQualsTo t q))
       else return [iat]
{-getSubItemAssocTypes iat@(iid,(LCA.DirectType (LCA.TyComp (LCA.CompTypeRef sueref knd _)) _ _)) | LCI.isAnonymousRef sueref = do
    dt <- LCA.getDefTable
    let mtd = getTagDef dt sueref
    case mtd of
         Nothing -> return []
         Just (LCA.CompDef (LCA.CompType _ _ mems _ _)) -> do
             subs <- liftM concat $ mapM (\md -> getSubItemAssocTypes $ getMemberSubItemAssoc iat md) mems
             return (iat : subs)-}
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

-- | For a function get the list of Add-Result properties.
-- The list has the same length as the list of regular parameters of the function.
-- An entry is true if the corresponding parameter has an effective (i.e. without Read-Only property) Add-Result property .
getAddResultProperties :: ItemAssocType -> FTrav [Bool]
getAddResultProperties iat@(_,(LCA.FunctionType (LCA.FunType _ pars _) _)) = 
    mapM shallAddResult $ map (getParamSubItemAssoc iat) (numberList pars)

-- | For a function get the name of the parameter with a specific Global-State property.
-- The first argument is the ItemAssocType of the function, the second is the Global-State property.
getGlobalStateParam :: ItemAssocType -> String -> FTrav String
getGlobalStateParam iat gs = do
    pids <- getGlobalStateSubItemIds iat
    gsps <- mapM getGlobalStateProperty pids
    return $ maybe "" (getParamName . snd) $ find (\(gsp,_) -> gsp == gs) $ zip gsps pids

-- | Retrieve the declaration for a global identifier (i.e. it has external or internal linkage).
getDeclWithLinkage :: LCI.Ident -> FTrav (Maybe LCA.IdentDecl)
getDeclWithLinkage ident = do
    mdecl <- LCA.lookupObject ident
    case mdecl of
         Nothing -> return Nothing
         Just decl -> do 
             case safeDeclLinkage decl of
                  LCA.NoLinkage -> return Nothing
                  _ -> return (Just decl)

-- | Retrieve information about a global object or function identifier used in a variable access in a function body.
-- If it has a Global-State property and a corresponding parameter has been declared for the function
-- the name of the parameter is returned as the first result component, otherwise the empty string.
-- If it has a Const-Val property the second result component is True, otherwise False.
getGlobalVarProperties :: LCI.Ident -> FTrav (String,Bool)
getGlobalVarProperties ident = do
    mdecl <- getDeclWithLinkage ident
    case mdecl of
         Nothing -> return $ ("",False)
         Just decl -> 
            if isFunction $ LCA.declType decl
               then return $ ("",False)
               else do
                   sfn <- getFileName
                   let iid = getIndividualItemId decl sfn
                   gs <- getGlobalStateProperty iid
                   mfdef <- getFunDef
                   case mfdef of
                        Just idecl@(LCA.FunctionDef _) -> do
                            let iat = getIndividualItemAssoc idecl sfn
                            gspar <- getGlobalStateParam iat gs
                            cv <- return False -- isConstValItem iid
                            return $ (gspar,cv)
                        _ -> return $ ("",False)

-- | Retrieve information about a (global) function identifier used for an invocation in a function body.
-- The first result component is a list of booleans telling for each regular parameter whether it has an Add-Result property.
-- The second result component is the list of parameter names of the surrounding function with Global-State property according
-- to those for the invoked function. The list corresponds to the Global-State parameters of the invoked function in their order.
-- If the surrounding function has no parameter with the same Global-State property the list contains an empty string.
-- The third result component contains the name of the heap parameter of the surrounding function, if both functions have the 
-- Heap-Use property, otherwise it is the empty string.
-- The fourth result component is the position of the parameter of the invoked function with a Modification-Function property,
-- otherwise it is -1.
getFunctionProperties :: LCI.Ident -> FTrav ([Bool],[String],String,Int)
getFunctionProperties ident = do
    mdecl <- getDeclWithLinkage ident
    case mdecl of
         Nothing -> return $ ([],[],"",-1)
         Just decl -> 
            if not $ isFunction $ LCA.declType decl
               then return $ ([],[],"",-1)
               else do
                   sfn <- getFileName
                   let iat = getIndividualItemAssoc decl sfn
                   arProps <- getAddResultProperties iat
                   pids <- getGlobalStateSubItemIds iat
                   gsps <- mapM getGlobalStateProperty pids
                   mfdef <- getFunDef
                   case mfdef of
                        Just idecl@(LCA.FunctionDef _) -> do
                            let fiat = getIndividualItemAssoc idecl sfn
                            gspars <- mapM (getGlobalStateParam fiat) $ sort gsps
                            hupar <- return "" -- determine hu param name
                            return $ (arProps, gspars,hupar,-1)
                        _ -> return $ ([],[],"",-1)
