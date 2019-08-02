{-# LANGUAGE PackageImports #-}
module Main where

import System.Environment (getArgs)
import Control.Monad (liftM)
import Data.List (sort)
import qualified Data.Map as M (lookup)

import qualified Language.C.Analysis as LCA
import Language.C.Analysis.DefTable (globalDefs)

import Gencot.Package (readPackageFromInput_,getIdentInvocations,getOwnCallGraphs,foldTables)
import Gencot.Json.Parmod (readParmodsFromFile)
import Gencot.Json.Process (convertParmods)
import Gencot.Traversal (runFTrav)
import Gencot.Cogent.Output (prettyTopLevels)
import Gencot.Cogent.Translate (transGlobals)
import Gencot.Util.Types (resolveTypedef)

main :: IO ()
main = do
    {- get arguments -}
    args <- getArgs
    {- get parameter modification descriptions and convert -}
    parmods <- (liftM convertParmods) (if null args then return [] else readParmodsFromFile $ head args)
    {- parse and analyse C sources and get global definitions -}
    tables <- readPackageFromInput_
    {- Determine all call graphs -}
    cgs <- getOwnCallGraphs tables
    {- combine symbol tables -}
    table <- foldTables tables
    let globals = globalDefs table
    {- Retrieve all invocations of named functions -}
    invks <- getIdentInvocations cgs
    {- reduce invocations to those external to the package -}
    let extInvks = filter (extFunDecFilter globals) invks
    {- wrap as DeclEvents and sort -}
    let extDecls = sort $ map LCA.DeclEvent extInvks
    {- translate external function declarations to Cogent abstract function definitions -}
    absdefs <- runFTrav table ("", parmods) $ transGlobals extDecls
    {- Output -}
    print $ prettyTopLevels absdefs

-- | Predicate for all non-variadic functions completely declared but not defined in g
extFunDecFilter :: LCA.GlobalDecls -> LCA.IdentDecl -> Bool
extFunDecFilter g decl@(LCA.Declaration _) =
    case resolveTypedef $ LCA.declType decl of
         LCA.FunctionType (LCA.FunType _ _ False) _ ->
            case M.lookup (LCA.declIdent decl) $ LCA.gObjs g of
              Nothing -> False
              (Just d) -> d == decl
         _ -> False
extFunDecFilter _ _ = False
