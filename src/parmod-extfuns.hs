{-# LANGUAGE PackageImports #-}
module Main where

import Control.Monad (liftM)
import qualified Data.Map as M (lookup)
import Data.List (union)

import Language.C.Analysis as LCA
import Language.C.Analysis.DefTable (globalDefs)

import Gencot.Package (readPackageFromInput,getIdentInvocations,getOwnCallGraphs,foldTables,foldTypeCarrierSets)
import Gencot.Json.Identifier (getFunId,getLocalFunId,getFunTypeId,getFunMemberId)
--import Gencot.Util.Types (collectUsedTypes,closeDerivedAndExternal,getFunctionTypeDefs,getFunctionMembers,getFunctionObjects,isFunction)
import Gencot.Util.Functions (getFunctionPars)
import Gencot.Util.Types (collectTypeCarriers,transCloseUsedCarriers,carriesNonPrimitive,getExtFunctionTypeDefs,getExtFunctionMembers,getFunctionObjects,isFunction,isFunPointerOptArr,isExtern)

main :: IO ()
main = do
--    {- parse and analyse C sources and get global definitions and used types -}
--    (tables,usedTypeSets) <- (liftM unzip) $ readPackageFromInput [] collectUsedTypes
    {- parse and analyse C sources and get global definitions and used types -}
    (tables,initialTypeCarrierSets) <- (liftM unzip) $ readPackageFromInput [] collectTypeCarriers
    {- Determine all call graphs -}
    cgs <- getOwnCallGraphs tables
    {- combine symbol tables -}
    table <- foldTables tables
    let globals = globalDefs table
--    {- combine sets of used types -}
--    let usedTypes = foldTypeSets usedTypeSets table
    {- combine sets of initial type carriers -}
    let initialTypeCarriers = foldTypeCarrierSets initialTypeCarrierSets table
    {- Retrieve all invocations of named functions -}
    invks <- getIdentInvocations cgs
    {- reduce invocations to those external to the package -}
    let extInvks = filter (extFunDecFilter globals) invks
    {- convert external invoked functions to parmod function ids -}
    let extInvkIds = map ((flip getFunId) "") extInvks
    {- get ids of function parameters of the external invoked functions -}
    let pExtInvkIds = map (uncurry getLocalFunId) $ getFunctionPars $ zip extInvkIds extInvks

    {- wrap as type carriers, filter functions with nonprimitive types -}
    let extFunDecls = filter carriesNonPrimitive $ map LCA.DeclEvent extInvks
    {- construct transitive closure of used type carriers -}
    let typeCarriers = transCloseUsedCarriers table (initialTypeCarriers ++ extFunDecls)
    {- Get the ids of objects with function pointer (array) type -}
    let objectIds = map ((flip getFunId) "") $ getFunctionObjects typeCarriers
    {- Get the ids of members with direct function (pointer (array)) type in used composite types -}
    let extMemberIds = map (uncurry getFunMemberId) $ getExtFunctionMembers typeCarriers
    {- Get the ids of used typedefs required by gencot-exttypes -}
    let extTypeDefIds = map getFunTypeId $ getExtFunctionTypeDefs typeCarriers

--    {- Determine non-primitive parameter and result types of the external invocations -}
--    let extInvkTypes = getParameterResultTypes extInvks
--    {- Complete used types and parameter and result types -}
--    let allUsedTypes = closeDerivedAndExternal table $ union usedTypes extInvkTypes
--    {- Get the ids of used external typedefs resolving to function (pointer (array)) types -}
--    let extTypeDefIds = map getFunTypeId $ getExternalFunTypeDefs table allUsedTypes
--    {- Get the id of members with direct function (pointer (array)) type in used external composite types -}
--    let extMemberIds = map (uncurry getFunMemberId) $ getExternalFunMembers table allUsedTypes
    {- Output -}
    putStrLn $ unlines $ extInvkIds ++ pExtInvkIds ++ objectIds ++ extMemberIds ++ extTypeDefIds

extFunDecFilter :: LCA.GlobalDecls -> LCA.IdentDecl -> Bool
extFunDecFilter g decl@(LCA.Declaration (LCA.Decl (LCA.VarDecl _ _ t) _)) =
    ((isFunction t) || 
     (isFunPointerOptArr t)) &&
    case M.lookup (LCA.declIdent decl) $ LCA.gObjs g of
         Nothing -> False
         (Just d) -> d == decl
extFunDecFilter _ _ = False
