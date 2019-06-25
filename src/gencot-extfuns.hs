{-# LANGUAGE PackageImports #-}
module Main where

import Data.List (sortBy)
import Data.Set (toList,Set,empty)

import qualified Language.C.Analysis as LCA
import qualified Language.C.Analysis.DefTable as LCD

import Gencot.Input (readFromInput_,getOwnDeclEvents,compEvent,getArgFileName,getParmodFileName)
import Gencot.Util.CallGraph (getCallGraph,CallGraph,getIdentInvokes)
import Gencot.Json.Parmod (readParmodsFromFile)
import Gencot.Traversal (runFTrav)
import Gencot.Cogent.Output (prettyTopLevels)
import Gencot.Cogent.Translate (transGlobals)

main :: IO ()
main = do
    {- parse and analyse C source and get global definitions -}
    table <- readFromInput_
    {- convert symbol table to list of declarations in processed file -}
    let decls = getOwnDeclEvents (LCD.globalDefs table) (\_ -> True)
    {- get call graph by traversing all function bodies in decls -}
    cg <- getCallGraph table decls
    {- todo: get list of declarations of invoked functions -}
    let invks = getIdentInvokes cg
    {- convert to list and filter externally complete declarations of non-variadic functions -}
    let extInvks = filter extDecFilter $ toList invks
    {- wrap as DeclEvents and sort -}
    let extDecls = sortBy compEvent $ map LCA.DeclEvent extInvks
    {- get own file name (may be needed for translating tag names) -}
    fnam <- getArgFileName
    {- get parameter modification descriptions -}
    pnam <- getParmodFileName
    parmods <- if null pnam then return [] else readParmodsFromFile pnam
    {- translate external function declarations to Cogent abstract function definitions -}
    absdefs <- runFTrav table (fnam,parmods) $ transGlobals extDecls
    {- Output -}
    print $ prettyTopLevels absdefs

extDecFilter :: LCA.IdentDecl -> Bool
extDecFilter (LCA.Declaration (LCA.Decl (LCA.VarDecl _ _ (LCA.FunctionType (LCA.FunType _ _ False) _)) _)) = True
extDecFilter _ = False
