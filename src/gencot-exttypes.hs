{-# LANGUAGE PackageImports #-}
module Main where

import System.Environment (getArgs)
import qualified Data.Map as M (lookup)
import Control.Monad (liftM)
import Data.List (sort)

import Language.C.Pretty (pretty)
import Language.C.Data.Ident
import qualified Language.C.Analysis as LCA
import Language.C.Analysis.DefTable (globalDefs)

import Gencot.Json.Parmod (readParmodsFromFile)
import Gencot.Json.Process (convertParmods)
import Gencot.Package (readPackageFromInput,getIdentInvocations,getOwnCallGraphs,foldTables,foldTypeCarrierSets)
import Gencot.Util.Types (collectTypeCarriers,transCloseUsedCarriers,carriesNonPrimitive,isFunction,isFunPointerOptArr,isExtern)
import Gencot.Traversal (runFTrav)
import Gencot.Cogent.Translate (transGlobals,transExtTypeDefs,genTypeDefs)
import Gencot.Cogent.Output (prettyTopLevels)

main :: IO ()
main = do
    {- get arguments -}
    args <- getArgs
    {- get parameter modification descriptions and convert -}
    parmods <- (liftM convertParmods) (if null args then return [] else readParmodsFromFile $ head args)
    {- parse and analyse C sources and get global definitions and used types -}
    (tables,initialTypeCarrierSets) <- (liftM unzip) $ readPackageFromInput [] collectTypeCarriers
    {- Determine all call graphs -}
    cgs <- getOwnCallGraphs tables
    {- combine symbol tables -}
    table <- foldTables tables
    let globals = globalDefs table
    {- combine sets of initial type carriers -}
    let initialTypeCarriers = foldTypeCarrierSets initialTypeCarrierSets table
    {- Retrieve all invocations of named functions -}
    invks <- getIdentInvocations cgs
    {- reduce invocations to functions external to the package -}
    let extInvks = filter (extFunDecFilter globals) invks
    {- wrap as type carriers, filter functions with nonprimitive types and sort -}
    let extFunDecls = sort $ filter carriesNonPrimitive $ map LCA.DeclEvent extInvks
    {- construct transitive closure of used type carriers -}
    let typeCarriers = transCloseUsedCarriers table (initialTypeCarriers ++ extFunDecls)
    {- translate type definitions in system include files -}
    extToplvs <- runFTrav table ("", parmods) $ transGlobals $ filter isExternTagDef typeCarriers
    extTypedefs <- runFTrav table ("", parmods) $ transExtTypeDefs $ filter isExternTypeDef typeCarriers
    {- generate abstract definitions for derived types in all type carriers -}
    derivedToplvs <- runFTrav table ("", parmods) $ genTypeDefs $ typeCarriers
    {- Output -}
    print $ prettyTopLevels (derivedToplvs ++ extToplvs ++ extTypedefs)

extFunDecFilter :: LCA.GlobalDecls -> LCA.IdentDecl -> Bool
extFunDecFilter g decl@(LCA.Declaration (LCA.Decl (LCA.VarDecl _ _ t) _)) =
    ((isFunction t) || 
     (isFunPointerOptArr t)) &&
    case M.lookup (LCA.declIdent decl) $ LCA.gObjs g of
         Nothing -> False
         (Just d) -> d == decl
extFunDecFilter _ _ = False

isExternTagDef :: LCA.DeclEvent -> Bool
isExternTagDef (LCA.TagEvent cd) = isExtern cd
isExternTagDef _ = False

isExternTypeDef :: LCA.DeclEvent -> Bool
isExternTypeDef (LCA.TypeDefEvent td) = isExtern td
isExternTypeDef _ = False
