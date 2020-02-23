{-# LANGUAGE PackageImports #-}
module Main where

import System.Environment (getArgs)
import Control.Monad (when,liftM)
import Data.List (sort)

import Language.C.Data.Ident (identToString)
import qualified Language.C.Analysis as LCA
import Language.C.Analysis.DefTable (globalDefs)

import Gencot.Input (getDeclEvents)
import Gencot.Items.Properties (readPropertiesFromFile)
import Gencot.Package (readPackageFromInput,getIdentInvocations,getOwnCallGraphs,foldTables,foldTypeCarrierSets)
import Gencot.Util.Types (collectTypeCarriers,transCloseUsedCarriers,usedTypeNames,carriesNonPrimitive,isExtern)
import Gencot.Traversal (runFTrav)
import Gencot.Cogent.Translate (transExtGlobals)
import Gencot.Cogent.Output (prettyTopLevels)

main :: IO ()
main = do
    {- get arguments -}
    args <- getArgs
    when (length args /= 2) 
        $ error "expected arguments: <items properties file name> <external items file name>"
    {- get item property map -}
    ipm <- readPropertiesFromFile $ head args
    {- get list of external items to process -}
    iids <- (liftM ((filter (not . null)) . lines)) $ readFile $ head $ tail args
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
    {- Get declarations of external invoked functions and invoked or listed items with nonprimitive types -}    
    let extDecls = filter carriesNonPrimitive $ getDeclEvents (globalDefs table) (constructFilter invks iids)
    {- build type carriers in the Cogent compilation unit by adding initial and external -}
    let unitTypeCarriers = initialTypeCarriers ++ extDecls
    {- Determine type names used directly in the Cogent compilation unit -}
    let unitTypeNames = usedTypeNames unitTypeCarriers
    {- construct transitive closure of used type carriers -}
    let typeCarriers = transCloseUsedCarriers table unitTypeCarriers
    {- translate type definitions in system include files -}
    toplvs <- runFTrav table ("",ipm,unitTypeNames) $ transExtGlobals unitTypeNames $ sort $ filter isExternDef typeCarriers
    {- Output -}
    print $ prettyTopLevels toplvs

isExternDef :: LCA.DeclEvent -> Bool
isExternDef (LCA.TagEvent cd) = isExtern cd
isExternDef (LCA.TypeDefEvent td) = isExtern td
isExternDef _ = False

constructFilter :: [LCA.IdentDecl] -> [String] -> LCA.DeclEvent -> Bool
constructFilter invks iids (LCA.DeclEvent decl@(LCA.Declaration _)) = invokedOrListed decl
    where invokedOrListed decl = elem decl invks || elem (identToString $ LCA.declIdent decl) iids
constructFilter _ _ _ = False
