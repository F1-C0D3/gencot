{-# LANGUAGE PackageImports #-}
module Main where

import System.Environment (getArgs)
import Data.List (sortBy)
import Data.Set (toList,Set,empty)
import Control.Monad (when)

import qualified Language.C.Analysis as LCA
import qualified Language.C.Analysis.DefTable as LCD

import Gencot.Input (readFromInput_,getOwnDeclEvents,compEvent)
import Gencot.Util.CallGraph (getCallGraph,CallGraph,getIdentInvokes)
import Gencot.Json.Parmod (readParmodsFromFile)
import Gencot.Json.Process (convertParmods)
import Gencot.Traversal (runFTrav)
import Gencot.Cogent.Output (prettyTopLevels)
import Gencot.Cogent.Translate (transGlobals)

main :: IO ()
main = do
    {- get and test arguments -}
    args <- getArgs
    when (null args || length args > 2) $ error "expected arguments: <original source file name> <parmod description file name>?"
    {- get own file name (may be needed for translating tag names) -}
    let fnam = head args
    {- get parameter modification descriptions -}
    parmods <- if length args == 1 then return [] else readParmodsFromFile $ head $ tail args
    {- parse and analyse C source and get global definitions -}
    table <- readFromInput_
    {- convert symbol table to list of declarations in processed file -}
    let decls = getOwnDeclEvents (LCD.globalDefs table) (\_ -> True)
    {- get call graph by traversing all function bodies in decls -}
    cg <- getCallGraph table decls
    {- get list of declarations of invoked functions -}
    let invks = getIdentInvokes cg
    {- convert to list and filter complete declarations of non-variadic functions -}
    let extInvks = filter extDecFilter $ toList invks
    {- wrap as DeclEvents and sort -}
    let extDecls = sortBy compEvent $ map LCA.DeclEvent extInvks
    {- translate external function declarations to Cogent abstract function definitions -}
    absdefs <- runFTrav table (fnam, convertParmods parmods) $ transGlobals extDecls
    {- Output -}
    print $ prettyTopLevels absdefs

extDecFilter :: LCA.IdentDecl -> Bool
extDecFilter (LCA.Declaration (LCA.Decl (LCA.VarDecl _ _ (LCA.FunctionType (LCA.FunType _ _ False) _)) _)) = True
extDecFilter _ = False
