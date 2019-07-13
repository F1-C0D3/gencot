{-# LANGUAGE PackageImports #-}
module Main where

import qualified Data.Map as M (lookup)

import Language.C.Analysis as LCA
import Language.C.Analysis.DefTable (globalDefs)

import Gencot.Package (readPackageFromInput,getFunctionInvocations,foldTables)
import Gencot.Json.Identifier (getFunId)

main :: IO ()
main = do
    {- parse and analyse C sources and get global definitions -}
    tables <- readPackageFromInput
    {- Determine all invoked functions -}
    invks <- getFunctionInvocations tables
    {- combine symbol tables -}
    table <- foldTables tables
    let globals = globalDefs table
    {- reduce invocations to those external to the package -}
    let extInvks = filter (extFunDecFilter globals) invks
    {- Convert to parmod function identifiers and output -}
    putStrLn $ unlines $ map ((flip getFunId) "") extInvks

extFunDecFilter :: LCA.GlobalDecls -> LCA.IdentDecl -> Bool
extFunDecFilter g decl@(LCA.Declaration (LCA.Decl (LCA.VarDecl _ _ (LCA.FunctionType _ _)) _)) =
    case M.lookup (LCA.declIdent decl) $ LCA.gObjs g of
         Nothing -> False
         (Just d) -> d == decl
extFunDecFilter _ _ = False


    

