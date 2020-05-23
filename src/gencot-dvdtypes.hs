{-# LANGUAGE PackageImports #-}
module Main where

import System.Environment (getArgs)
import Control.Monad (when,liftM,mapM)
import Data.Map (toList,unions)

import Language.C.Data.Ident (identToString)
import qualified Language.C.Analysis as LCA
import Language.C.Analysis.DefTable (globalDefs)

import Gencot.Input (getDeclEvents)
import Gencot.Items.Identifier (getTypedefNames)
import Gencot.Items.Properties (readPropertiesFromFile)
import Gencot.Items.Types (getItemAssocType,getTagItemId,getTypedefItemId)
import Gencot.Package (readPackageFromInput,foldTables,foldTypeCarrierSets)
import Gencot.Util.Types (collectTypeCarriers,carriesNonPrimitive,isExtern)
import Gencot.Names (readNameMapFromFile)
import Gencot.Traversal (runFTrav,runWithTable)
import Gencot.Cogent.Translate (genTypeDefs,genDerivedTypeNames)
import Gencot.Cogent.Output (prettyTopLevels)

main :: IO ()
main = do
    {- get arguments -}
    args <- getArgs
    when (length args /= 3) 
        $ error "expected arguments: <name prefix map> <item property file name> <external items file name>"
    {- get name prefix map -}
    npm <- readNameMapFromFile $ head args
    {- get item property map -}
    ipm <- readPropertiesFromFile $ head $ tail args
    {- get list of used external items -}
    useditems <- (liftM ((filter (not . null)) . lines)) $ readFile $ head $ tail $ tail args
    {- parse and analyse C sources and get global definitions and used types -}
    (tables,initialTypeCarrierSets) <- (liftM unzip) $ readPackageFromInput [] (collectTypeCarriers carriesNonPrimitive)
    {- combine symbol tables -}
    table <- foldTables tables
    {- combine sets of initial type carriers -}
    let initialTypeCarriers = foldTypeCarrierSets initialTypeCarrierSets table
    {- Get declarations of used external functions and objects -}    
    let extDecls = getDeclEvents (globalDefs table) (constructFilter useditems)
    {- build type carriers in the Cogent compilation unit by adding initial and external -}
    let unitTypeCarriers = initialTypeCarriers ++ extDecls
    {- Determine external type names used directly in the Cogent compilation unit -}
    let unitTypeNames = getTypedefNames useditems
    {- generate abstract definitions for derived types in all type carriers -}
    toplvs <- runFTrav table ("", npm, ipm,(True,unitTypeNames)) $ genTypeDefs unitTypeCarriers
    {- Output -}
    print $ prettyTopLevels toplvs

constructFilter :: [String] -> LCA.DeclEvent -> Bool
constructFilter iids (LCA.DeclEvent decl@(LCA.Declaration _)) = 
    elem (identToString $ LCA.declIdent decl) iids
constructFilter iids (LCA.TagEvent td@(LCA.CompDef ct)) = 
    isExtern td && elem (getTagItemId ct "") iids
constructFilter iids (LCA.TypeDefEvent td@(LCA.TypeDef idnam _ _ _)) = 
    isExtern td && elem (getTypedefItemId idnam) iids
constructFilter _ _ = False
