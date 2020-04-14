{-# LANGUAGE PackageImports #-}
module Main where

import System.Environment (getArgs)
import Control.Monad (liftM,when)
import Data.List (nub)

import Language.C.Analysis as LCA
import Language.C.Data.Ident (identToString,isAnonymousRef)
import Language.C.Analysis.DefTable (globalDefs)

import Gencot.Input (getDeclEvents)
import Gencot.Package (readPackageFromInput,getIdentInvocations,getOwnCallGraphs,foldTables,foldTypeCarrierSets)
import Gencot.Util.Types (collectTypeCarriers,transCloseUsedCarriers,carriesNamedType,usedTypeNames,externTypeNames,isExtern, transCloseCarriers,usedCarriers)
import Gencot.Items.Types (getItemAssocType,getExternalItemId,getTypedefItemId,getTagItemId,getEnumItemId)
import Gencot.Traversal (runWithTable)

main :: IO ()
main = do
    {- get arguments -}
    args <- getArgs
    when (null args || length args > 1) $ error "expected arguments: <additional items file name>"
    {- get list of additional external items to process -}
    additems <- (liftM ((filter (not . null)) . lines)) (readFile $ head args)
    {- parse and analyse C sources and get global definitions and used types -}
    (tables,initialTypeCarrierSets) <- (liftM unzip) $ readPackageFromInput [] (collectTypeCarriers carriesNamedType)
    {- Determine all call graphs -}
    cgs <- getOwnCallGraphs tables
    {- Retrieve all invocations of named functions -}
    invks <- getIdentInvocations cgs
    {- combine symbol tables -}
    table <- foldTables tables
    {- combine sets of initial type carriers -}
    let initialTypeCarriers = foldTypeCarrierSets initialTypeCarrierSets table
    {- Get declarations of external functions and objects which are invoked or additionally specified -}
    let extDecls = getDeclEvents (globalDefs table) (extDeclFilter invks additems)
    {- Get definitions of additionally specified external tags and type names -}
    let extTypes = getDeclEvents (globalDefs table) (extTypeFilter additems)
    {- build directly used type carriers by adding initial and filtered external -}
    let unitTypeCarriers = initialTypeCarriers ++ filter carriesNamedType extDecls
    {- Determine type names used directly in the Cogent compilation unit or additionally specified-}
    let unitTypeNames = (usedTypeNames unitTypeCarriers) ++ (externTypeNames extTypes)
    {- construct transitive closure of used type carriers -}
    let typeCarriers = transCloseUsedCarriers table (unitTypeCarriers ++ extTypes)
    {- construct item associated types for external functions/objects and used named type carriers -}
    iats <- runWithTable table $ mapM getItemAssocType $ nub ((filter (isExternNamedDef unitTypeNames) typeCarriers) ++ extDecls)
    {- Output -}
    putStrLn $ unlines $ map fst iats

isExternNamedDef :: [String] -> LCA.DeclEvent -> Bool
isExternNamedDef _ (LCA.TagEvent cd) = isExtern cd && (not $ isAnonymousRef $ LCA.sueRef cd)
isExternNamedDef utn (LCA.TypeDefEvent td) = isExtern td && (elem (identToString $ LCA.identOfTypeDef td) utn)
isExternNamedDef _ _ = False

extDeclFilter :: [LCA.IdentDecl] -> [String] -> LCA.DeclEvent -> Bool
extDeclFilter invks iids (LCA.DeclEvent decl@(LCA.Declaration _)) = invokedOrListed decl
    where invokedOrListed decl = elem decl invks || elem (getExternalItemId decl) iids
extDeclFilter _ _ _ = False

extTypeFilter :: [String] -> LCA.DeclEvent -> Bool
extTypeFilter iids (LCA.TagEvent td@(LCA.CompDef (LCA.CompType sueref knd _ _ _))) = 
    isExtern td && elem (getTagItemId sueref knd) iids
extTypeFilter iids (LCA.TagEvent td@(LCA.EnumDef (LCA.EnumType sueref _ _ _))) = 
    isExtern td && elem (getEnumItemId sueref) iids
extTypeFilter iids (LCA.TypeDefEvent td@(LCA.TypeDef idnam _ _ _)) = 
    isExtern td && elem (getTypedefItemId idnam) iids
extTypeFilter _ _ = False

