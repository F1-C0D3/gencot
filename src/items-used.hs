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
import Gencot.Util.Types (collectTypeCarriers,transCloseUsedCarriers,carriesNonPrimitive,usedTypeNames,isExtern)
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
    (tables,initialTypeCarrierSets) <- (liftM unzip) $ readPackageFromInput [] collectTypeCarriers
    {- Determine all call graphs -}
    cgs <- getOwnCallGraphs tables
    {- combine symbol tables -}
    table <- foldTables tables
    {- combine sets of initial type carriers -}
    let initialTypeCarriers = foldTypeCarrierSets initialTypeCarrierSets table
    {- Retrieve all invocations of named functions -}
    invks <- getIdentInvocations cgs
    {- Get declarations of external functions and objects which are invoked or additionally specified -}
    {- and of additionally specified external tags and type names -}
    let extDecls = getDeclEvents (globalDefs table) (constructFilter invks additems)
    {- build directly used type carriers by adding initial and filtered external -}
    let unitTypeCarriers = initialTypeCarriers ++ filter carriesNonPrimitive extDecls
    {- construct transitive closure of used type carriers -}
    let typeCarriers = transCloseUsedCarriers table unitTypeCarriers
    {- Determine type names used directly in the Cogent compilation unit -}
    let unitTypeNames = usedTypeNames unitTypeCarriers
    {- construct item associated types for external functions/objects and used named type carriers -}
    iats <- runWithTable table $ mapM (getItemAssocType unitTypeNames) $ nub ((filter isExternNamedDef typeCarriers) ++ extDecls)
    {- Output -}
    putStrLn $ unlines $ map fst iats

isExternNamedDef :: LCA.DeclEvent -> Bool
isExternNamedDef (LCA.TagEvent cd) = isExtern cd && (not $ isAnonymousRef $ LCA.sueRef cd)
isExternNamedDef (LCA.TypeDefEvent td) = isExtern td
isExternNamedDef _ = False

constructFilter :: [LCA.IdentDecl] -> [String] -> LCA.DeclEvent -> Bool
constructFilter invks iids (LCA.DeclEvent decl@(LCA.Declaration _)) = invokedOrListed decl
    where invokedOrListed decl = elem decl invks || elem (getExternalItemId decl) iids
constructFilter _ iids (LCA.TagEvent td@(LCA.CompDef (LCA.CompType sueref knd _ _ _))) = 
    isExtern td && elem (getTagItemId sueref knd) iids
constructFilter _ iids (LCA.TagEvent td@(LCA.EnumDef (LCA.EnumType sueref _ _ _))) = 
    isExtern td && elem (getEnumItemId sueref) iids
constructFilter _ iids (LCA.TypeDefEvent td@(LCA.TypeDef idnam _ _ _)) = 
    isExtern td && elem (getTypedefItemId idnam) iids
constructFilter _ _ _ = False
