{-# LANGUAGE PackageImports #-}
module Main where

import System.Environment (getArgs)
import Control.Monad (when)
import Data.List (sortBy)
import qualified Data.Map as M (lookup)

import qualified Language.C.Analysis as LCA
import Language.C.Analysis.DefTable (globalDefs)

import Gencot.Package (readPackageFromInput,getFunctionInvocations,foldTables)
import Gencot.Input (compEvent)
import Gencot.Json.Parmod (readParmodsFromFile)
import Gencot.Json.Process (convertParmods)
import Gencot.Traversal (runFTrav)
import Gencot.Cogent.Output (prettyTopLevels)
import Gencot.Cogent.Translate (transGlobals)

main :: IO ()
main = do
    {- get arguments -}
    args <- getArgs
    {- get parameter modification descriptions -}
    parmods <- if null args then return [] else readParmodsFromFile $ head args
    {- parse and analyse C sources and get global definitions -}
    tables <- readPackageFromInput
    {- Determine all invoked functions -}
    invks <- getFunctionInvocations tables
    {- combine symbol tables -}
    table <- foldTables tables
    let globals = globalDefs table
    {- reduce invocations to those external to the package -}
    let extInvks = filter (extFunDecFilter globals) invks
    {- wrap as DeclEvents and sort -}
    let extDecls = sortBy compEvent $ map LCA.DeclEvent extInvks
    {- translate external function declarations to Cogent abstract function definitions -}
    absdefs <- runFTrav table ("", convertParmods parmods) $ transGlobals extDecls
    {- Output -}
    print $ prettyTopLevels absdefs

-- | Predicate for all non-variadic functions completely declared but not defined in g
extFunDecFilter :: LCA.GlobalDecls -> LCA.IdentDecl -> Bool
extFunDecFilter g decl@(LCA.Declaration (LCA.Decl (LCA.VarDecl _ _ (LCA.FunctionType (LCA.FunType _ _ False) _)) _)) =
    case M.lookup (LCA.declIdent decl) $ LCA.gObjs g of
         Nothing -> False
         (Just d) -> d == decl
extFunDecFilter _ _ = False
