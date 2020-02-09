module Gencot.Items.Translate where

import Control.Monad (liftM)
import Data.Map (unions,fromList)

import Language.C.Analysis as LCA

import Gencot.Items.Properties (ItemProperties)
import Gencot.Items.Types (ItemAssocType,getItemAssocTypes,getSubItemAssocTypes)
import Gencot.Items.Identifier (defaultItemId)
import Gencot.Traversal (FTrav)
import Gencot.Util.Types (isReadOnlyType,isFunction,isPointer,isFunPointer)

-- | Translate a sequence of C "external" (global) declarations to an item property map.
transGlobals :: [LCA.DeclEvent] -> FTrav ItemProperties
transGlobals tcs = liftM unions $ mapM transGlobal tcs

-- | Translate a C "external" (global) declaration to an item property map
-- Retrieve the item associated type(s) of the declaration,
-- (resolving the types of external items without stopping at used type names
-- since we do not know them here and they do not matter for the default properties),
-- retrieve all sub-items with their types,
-- filter function types and non-function pointer types,
-- determine the default properties for them 
-- and return them as an item property map.
transGlobal :: LCA.DeclEvent -> FTrav ItemProperties
transGlobal tc = do
    iats <- getItemAssocTypes [] tc
    iats <- liftM concat $ mapM getSubItemAssocTypes iats
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
