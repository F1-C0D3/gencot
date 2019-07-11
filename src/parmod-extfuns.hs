{-# LANGUAGE PackageImports #-}
module Main where

import Data.List (sortBy)
import Data.Set (toList,unions)
import Data.Map as M (lookup)
import Control.Monad (liftM)

import qualified Language.C.Analysis as LCA
import qualified Language.C.Analysis.DefTable as LCD

import Gencot.Input (readPackageFromInput,getOwnDeclEvents,compEvent)
import Gencot.SymTab (debugTable,foldTables)
import Gencot.Util.CallGraph (getCallGraph,CallGraph,getIdentInvokes)
import Gencot.Json.Identifier (getFunId)

main :: IO ()
main = do
    {- parse and analyse C sources and get global definitions -}
    tables <- readPackageFromInput
    --mapM debugTable tables
    {- convert symbol table to list of declarations in processed file -}
    let decls = map (\tab -> getOwnDeclEvents (LCD.globalDefs tab) (\_ -> True)) tables
    {- get call graphs by traversing all function bodies in decls -}
    cgs <- mapM (uncurry getCallGraph) $ zip tables decls
    {- get lists of declarations of invoked functions -}
    let invks = filter funDecFilter $ toList $ unions $ map getIdentInvokes cgs
    {- combine symbol tables -}
    table <- foldTables tables
    --debugTable table
    let globals = LCD.globalDefs table
    {- reduce invocations to those external to the package -}
    let extInvks = filter (extFilter globals) invks
    {- Convert to parmod function identifiers and output -}
    putStrLn $ unlines $ map ((flip getFunId) "") extInvks

funDecFilter :: LCA.IdentDecl -> Bool
funDecFilter (LCA.Declaration (LCA.Decl (LCA.VarDecl _ _ (LCA.FunctionType _ _)) _)) = True
funDecFilter _ = False

extFilter :: LCA.GlobalDecls -> LCA.IdentDecl -> Bool
extFilter g decl = case M.lookup (LCA.declIdent decl) $ LCA.gObjs g of
                        Nothing -> False
                        (Just d) -> d == decl
