{-# LANGUAGE PackageImports #-}
module Main where

import System.Environment (getArgs)
import Control.Monad (when,liftM)

import Language.C.Data.Ident (identToString)
import qualified Language.C.Analysis as LCA
import Language.C.Analysis.DefTable (globalDefs)

import Gencot.Input (getDeclEvents)
import Gencot.Items.Identifier (getTypedefNames)
import Gencot.Items.Properties (readPropertiesFromFile)
import Gencot.Package (readPackageFromInput,foldTables,foldTypeCarrierSets)
import Gencot.Util.Types (collectTypeCarriers,carriesNonPrimitive)
import Gencot.Traversal (runFTrav)
import Gencot.Cogent.Translate (genTypeDefs)
import Gencot.Cogent.Output (prettyTopLevels)

main :: IO ()
main = do
    {- get arguments -}
    args <- getArgs
    when (length args /= 2) 
        $ error "expected arguments: <item property file name> <external items file name>"
    {- get item property map -}
    ipm <- readPropertiesFromFile $ head args
    {- get list of external items to process -}
    iids <- (liftM ((filter (not . null)) . lines)) $ readFile $ head $ tail args
    {- parse and analyse C sources and get global definitions and used types -}
    (tables,initialTypeCarrierSets) <- (liftM unzip) $ readPackageFromInput [] collectTypeCarriers
    {- combine symbol tables -}
    table <- foldTables tables
    {- combine sets of initial type carriers -}
    let initialTypeCarriers = foldTypeCarrierSets initialTypeCarrierSets table
    {- Get declarations of used external functions and objects with nonprimitive types -}    
    let extDecls = filter carriesNonPrimitive $ getDeclEvents (globalDefs table) (constructFilter iids)
    {- build type carriers in the Cogent compilation unit by adding initial and external -}
    let unitTypeCarriers = initialTypeCarriers ++ extDecls
    {- Determine external type names used directly in the Cogent compilation unit -}
    let unitTypeNames = getTypedefNames iids
    {- generate abstract definitions for derived types in all type carriers -}
    toplvs <- runFTrav table ("", ipm,unitTypeNames) $ genTypeDefs unitTypeNames $ unitTypeCarriers
    {- Output -}
    print $ prettyTopLevels toplvs

constructFilter :: [String] -> LCA.DeclEvent -> Bool
constructFilter iids (LCA.DeclEvent decl@(LCA.Declaration _)) = 
    elem (identToString $ LCA.declIdent decl) iids
constructFilter _ _ = False
