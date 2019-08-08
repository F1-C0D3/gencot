{-# LANGUAGE PackageImports #-}
module Main where

import System.Environment (getArgs)
import Control.Monad (liftM)

import Language.C.Analysis as LCA
import Language.C.Data.Ident (identToString)
import Language.C.Analysis.DefTable (globalDefs)

import Gencot.Input (getDeclEvents)
import Gencot.Package (readPackageFromInput,getIdentInvocations,getOwnCallGraphs,foldTables,foldTypeCarrierSets)
import Gencot.Json.Identifier (getFunId,getLocalFunId,getFunTypeId,getFunMemberId)
import Gencot.Util.Functions (getFunctionPars)
import Gencot.Util.Types (collectTypeCarriers,transCloseUsedCarriers,carriesNonPrimitive,usedTypeNames,getExtFunctionTypeDefs,getExtFunctionMembers,isFunction,isFunPointerOptArr,isExtern)

main :: IO ()
main = do
    {- get arguments -}
    args <- getArgs
    {- get list of external variables to process -}
    varnams <- (liftM ((filter (not . null)) . lines)) (if null args then return "" else readFile $ head args)
    {- parse and analyse C sources and get global definitions and used types -}
    (tables,initialTypeCarrierSets) <- (liftM unzip) $ readPackageFromInput [] collectTypeCarriers
    {- Determine all call graphs -}
    cgs <- getOwnCallGraphs tables
    {- combine symbol tables -}
    table <- foldTables tables
    {- combine sets of initial type carriers -}
    let initialTypeCarriers = foldTypeCarrierSets initialTypeCarrierSets table
    {- Retrieve all invocations of named functions -}
    invks <- getIdentInvocations cgs
    {- Get declarations of external invoked functions and invoked or listed variables -}    
    let extDecls = getDeclEvents (globalDefs table) (constructFilter invks varnams)
    {- add parmod function ids to functions and function pointer (array)s -}
    let extFunDeclsWithIds = map ((\idecl -> (getFunId idecl "",idecl)) . getIdentDecl) $ filter funDecFilter extDecls
    {- get ids of function parameters of the functions -}
    let pExtInvkIds = map (uncurry getLocalFunId) $ getFunctionPars $ filter funFilter extFunDeclsWithIds
    {- build type carriers in the Cogent compilation unit by adding initial and filtered external -}
    let unitTypeCarriers = initialTypeCarriers ++ filter carriesNonPrimitive extDecls
    {- Determine type names used directly in the Cogent compilation unit -}
    let unitTypeNames = usedTypeNames unitTypeCarriers
    {- construct transitive closure of used type carriers -}
    let typeCarriers = transCloseUsedCarriers table unitTypeCarriers
    {- Get the ids of members with direct function (pointer (array)) type in used composite types -}
    let extMemberIds = map (uncurry getFunMemberId) $ getExtFunctionMembers typeCarriers
    {- Get the ids of used typedefs required by gencot-exttypes -}
    let extTypeDefIds = map getFunTypeId $ getExtFunctionTypeDefs typeCarriers
    {- Output -}
    putStrLn $ unlines $ (map fst extFunDeclsWithIds) ++ pExtInvkIds ++ extMemberIds ++ extTypeDefIds

constructFilter :: [LCA.IdentDecl] -> [String] -> LCA.DeclEvent -> Bool
constructFilter invks varnams (LCA.DeclEvent decl@(LCA.Declaration _)) = invokedOrListed decl
    where invokedOrListed decl = elem decl invks || elem (identToString $ LCA.declIdent decl) varnams
constructFilter _ _ _ = False

funDecFilter :: LCA.DeclEvent -> Bool
funDecFilter (LCA.DeclEvent (LCA.Declaration (LCA.Decl (LCA.VarDecl _ _ t) _))) =
    (isFunction t) || (isFunPointerOptArr t)

getIdentDecl (LCA.DeclEvent decl) = decl

funFilter :: (String,LCA.IdentDecl) -> Bool
funFilter (_,(LCA.Declaration (LCA.Decl (LCA.VarDecl _ _ t) _))) = isFunction t
