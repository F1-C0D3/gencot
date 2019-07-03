{-# LANGUAGE PackageImports #-}
module Main where

import Data.List (sortBy)
import Data.Set (toList)

import qualified Language.C.Analysis as LCA
import qualified Language.C.Analysis.DefTable as LCD

import Gencot.Input (readPackageFromInput_,getOwnDeclEvents,compEvent)
import Gencot.Util.CallGraph (getCallGraph,CallGraph,getIdentInvokes)
import Gencot.Json.Identifier (getFunId)

main :: IO ()
main = do
    {- parse and analyse C source and get global definitions -}
    table <- readPackageFromInput_
    {- convert symbol table to list of declarations in processed file -}
    let decls = getOwnDeclEvents (LCD.globalDefs table) (\_ -> True)
    {- get call graph by traversing all function bodies in decls -}
    cg <- getCallGraph table decls
    {- get list of declarations of invoked functions -}
    let invks = getIdentInvokes cg
    {- convert to list and filter function declarations -}
    let extInvks = filter extDecFilter $ toList invks
    {- Convert to parmod function identifiers and output -}
    putStrLn $ unlines $ map ((flip getFunId) "") extInvks

extDecFilter :: LCA.IdentDecl -> Bool
extDecFilter (LCA.Declaration (LCA.Decl (LCA.VarDecl _ _ (LCA.FunctionType _ _)) _)) = True
extDecFilter _ = False
