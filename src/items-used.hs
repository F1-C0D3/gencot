{-# LANGUAGE PackageImports #-}
module Main where

import System.Environment (getArgs)
import Control.Monad (liftM,when)

import Language.C.Analysis as LCA
import Language.C.Data.Ident (identToString)
import Language.C.Analysis.DefTable (globalDefs)

import Gencot.Input (getDeclEvents)
import Gencot.Package (readPackageFromInput,getIdentInvocations,getOwnCallGraphs,foldTables,foldTypeCarrierSets)
import Gencot.Util.Types (collectTypeCarriers,transCloseUsedCarriers,carriesNonPrimitive,usedTypeNames,isExtern)
import Gencot.Items.Types (getItemAssocType)
import Gencot.Traversal (runWithTable)

main :: IO ()
main = do
    {- get arguments -}
    args <- getArgs
    when (null args || length args > 1) $ error "expected arguments: <additional items file name>"
    {- get list of additional external items to process -}
    additems <- (liftM ((filter (not . null)) . lines)) (readFile $ head args)
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
    {- Get declarations of external invoked functions and invoked or additionally specified variables -}    
    let extDecls = getDeclEvents (globalDefs table) (constructFilter invks additems)
    {- build type carriers in the Cogent compilation unit by adding initial and filtered external -}
    let unitTypeCarriers = initialTypeCarriers ++ filter carriesNonPrimitive extDecls
    {- construct transitive closure of used type carriers -}
    let typeCarriers = transCloseUsedCarriers table unitTypeCarriers
    {- Determine type names used directly in the Cogent compilation unit -}
    let unitTypeNames = usedTypeNames unitTypeCarriers
    {- construct item associated types for external functions/objects and used type carriers -}
    iats <- runWithTable table $ mapM (getItemAssocType unitTypeNames) (extDecls ++ (filter isExternDef typeCarriers))
    {- Output -}
    putStrLn $ unlines $ map fst iats

isExternDef :: LCA.DeclEvent -> Bool
isExternDef (LCA.TagEvent cd) = isExtern cd
isExternDef (LCA.TypeDefEvent td) = isExtern td
isExternDef _ = False

constructFilter :: [LCA.IdentDecl] -> [String] -> LCA.DeclEvent -> Bool
constructFilter invks iids (LCA.DeclEvent decl@(LCA.Declaration _)) = invokedOrListed decl
    where invokedOrListed decl = elem decl invks || elem (identToString $ LCA.declIdent decl) iids
constructFilter _ _ _ = False

