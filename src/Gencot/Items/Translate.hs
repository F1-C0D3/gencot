module Gencot.Items.Translate where

import Control.Monad (liftM)
import Data.Map (unions,fromList)

import Language.C.Analysis as LCA

import Gencot.Items.Properties (ItemProperties)
import Gencot.Items.Types (ItemAssocType,getItemAssocType,getMemberItemAssocTypes,getSubItemAssocTypes)
import Gencot.Items.Identifier (defaultItemId,isParameterId,isEmbeddedId)
import Gencot.Traversal (FTrav)
import Gencot.Util.Types (isReadOnlyType,isLinearParType,isFunction,isPointer,isArray,isFunPointer,isComposite,isLeafType,resolveTypedef)

-- | Translate a sequence of C "external" (global) declarations to an item property map.
-- First argument is stop-resolve typenames, this will be removed when they are retrieved from the user state.
transGlobals :: [String] -> [LCA.DeclEvent] -> FTrav ItemProperties
transGlobals tds tcs = liftM unions $ mapM (transGlobal tds) tcs

-- | Translate a C "external" (global) declaration to an item property map
-- Retrieve the item associated type(s) of the declaration,
-- retrieve all sub-items with their types,
-- filter function types, array types, and non-function pointer types,
-- determine the default properties for them 
-- and return them as an item property map.
transGlobal :: [String] -> LCA.DeclEvent -> FTrav ItemProperties
transGlobal tds tc = do
    iat <- getItemAssocType tc
    miats <- getMemberItemAssocTypes tc
    iats <- liftM concat $ mapM getSubItemAssocTypes (iat : miats)
    let fiats = filter (\(iid,t) -> (not $ isLeafType $ resolveTypedef t) 
                                    && (not $ isFunPointer t) 
                                    && ((isParameterId iid) || (not $ isComposite t))) iats
    dip <- mapM getDefaultProperies fiats
    return $ fromList dip

-- | Get the default properties for an item associated type.
-- If the type is a pointer type with all contained pointers qualified as const the ro property is used,
-- if the identifier is for a parameter and the type is linear and no ro property the ar property is used,
-- otherwise no property is used.
getDefaultProperies :: ItemAssocType -> FTrav (String,[String])
getDefaultProperies (iid,t) = do
    ro <- isReadOnlyType t
    lt <- isLinearParType t
    let roProp = if ro && ((isPointer t) || ((isArray t) && (not $ isEmbeddedId iid))) then ["ro"] else []
    let arProp = if lt && (isParameterId iid) then ["ar"] else []
    return (defaultItemId iid,roProp ++ arProp)
