module Gencot.Items.Translate where

import Control.Monad (liftM)
import Data.Map (unions,fromList)

import Language.C.Analysis as LCA

import Gencot.Items.Properties (ItemProperties)
import Gencot.Items.Types (ItemAssocType,getItemAssocType,getMemberItemAssocTypes,getSubItemAssocTypes)
import Gencot.Items.Identifier (defaultItemId)
import Gencot.Traversal (FTrav)
import Gencot.Util.Types (isReadOnlyType,isFunction,isPointer,isFunPointer)

-- | Translate a sequence of C "external" (global) declarations to an item property map.
-- First argument is stop-resolve typenames, this will be removed when they are retrieved from the user state.
transGlobals :: [String] -> [LCA.DeclEvent] -> FTrav ItemProperties
transGlobals tds tcs = liftM unions $ mapM (transGlobal tds) tcs

-- | Translate a C "external" (global) declaration to an item property map
-- Retrieve the item associated type(s) of the declaration,
-- retrieve all sub-items with their types,
-- filter function types and non-function pointer types,
-- determine the default properties for them 
-- and return them as an item property map.
transGlobal :: [String] -> LCA.DeclEvent -> FTrav ItemProperties
transGlobal tds tc = do
    iat <- getItemAssocType tds tc
    miats <- getMemberItemAssocTypes tc
    iats <- liftM concat $ mapM getSubItemAssocTypes (iat : miats)
    let fiats = filter (\(_,t) -> (isFunction t) || ((isPointer t) && (not $ isFunPointer t))) iats
    dip <- mapM getDefaultProperies fiats
    return $ fromList dip

-- | Get the default properties for an item associated type.
-- If the type is a pointer type with all contained pointers qualified as const the ro property is used,
-- otherwise no property is used.
getDefaultProperies :: ItemAssocType -> FTrav (String,[String])
getDefaultProperies (iid,t) = do
    ro <- isReadOnlyType t
    if ro && isPointer t then return (diid,["ro"]) else return (diid,[])
    where diid = defaultItemId iid
