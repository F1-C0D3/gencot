{-# LANGUAGE PackageImports #-}
module Main where

import System.Environment (getArgs)
import Control.Monad (when,liftM)
import Data.Map (empty)
import Data.List (nub)

import Language.C.Pretty (pretty)
import Language.C.Data.Ident (identToString)
import qualified Language.C.Analysis as LCA
import Language.C.Analysis.DefTable (globalDefs)

import Gencot.Input (getDeclEvents)
import Gencot.Json.Parmod (readParmodsFromFile)
import Gencot.Json.Process (convertParmods)
import Gencot.Package (readPackageFromInput,getIdentInvocations,getOwnCallGraphs,foldTables,foldTypeCarrierSets)
import Gencot.Util.Types (collectTypeCarriers,transCloseUsedCarriers,usedTypeNames,carriesNonPrimitive)
import Gencot.Traversal (runFTrav)
import Gencot.Cogent.Translate (genTypeDefs)
import Gencot.Cogent.Output (prettyTopLevels)

main :: IO ()
main = do
    {- get arguments -}
    args <- getArgs
    when (length args < 2 || length args > 3) 
        $ error "expected arguments: <safe pointer list file name> <external variables list file name> <parmod description file name>?"
    {- get list of safe pointers -}
    spl <- (liftM ((filter (not . null)) . lines)) $ readFile $ head args
    {- get list of external variables to process -}
    varnams <- (liftM ((filter (not . null)) . lines)) $ readFile $ head $ tail args
    {- get parameter modification descriptions and convert -}
    parmods <- (liftM convertParmods) (if 3 > length args then return [] else readParmodsFromFile $ head $ tail $ tail args)
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
    {- Get declarations of external invoked functions and invoked or listed variables with nonprimitive types -}    
    let extDecls = filter carriesNonPrimitive $ getDeclEvents (globalDefs table) (constructFilter invks varnams)
    {- build type carriers in the Cogent compilation unit by adding initial and external -}
    let unitTypeCarriers = initialTypeCarriers ++ extDecls
    {- Determine type names used directly in the Cogent compilation unit -}
    let unitTypeNames = usedTypeNames unitTypeCarriers
    {- construct transitive closure of used type carriers -}
    let typeCarriers = transCloseUsedCarriers table unitTypeCarriers
    {- generate abstract definitions for derived types in all type carriers -}
    toplvs <- runFTrav table ("", parmods,nub spl,unitTypeNames) $ genTypeDefs unitTypeNames $ typeCarriers
    {- Output -}
    print $ prettyTopLevels toplvs

constructFilter :: [LCA.IdentDecl] -> [String] -> LCA.DeclEvent -> Bool
constructFilter invks varnams (LCA.DeclEvent decl@(LCA.Declaration _)) = invokedOrListed decl
    where invokedOrListed decl = elem decl invks || elem (identToString $ LCA.declIdent decl) varnams
constructFilter _ _ _ = False
