{-# LANGUAGE PackageImports #-}
module Main where

import System.Environment (getArgs)
import Text.JSON (encode)
import Text.Pretty.Simple (pStringNoColor)
import Data.Text.Lazy (unpack)

import Language.C.Analysis
import Language.C.Analysis.DefTable (globalDefs)

import Gencot.Input (readFromInput_,getDeclEvents,getOwnDeclEvents,getArgFileName)
import Gencot.Util.CallGraph (getCallGraph,runWithCallGraph)
import Gencot.Json.Translate (transGlobals)
import Gencot.Json.Process (readParmods,addParsFromInvokes)
import Gencot.Traversal (runWithTable)

main :: IO ()
main = do
    {- parse and analyse C source and get global definitions -}
    table <- readFromInput_
    {- get input file name -}
    fnam <- getArgFileName
    {- get arguments and test for close option -}
    args <- getArgs
    let close = (length args) > 1
    {- convert symbol table to list of constructs to be processed -}
    let globals = if close
                    then getDeclEvents (globalDefs table) declFilter
                    else getOwnDeclEvents (globalDefs table) defFilter
    {- get call graph -}
    cg <- getCallGraph table globals
    {- translate functions to Json parmod template -}
    parmodtmpl <- runWithCallGraph cg table fnam $ transGlobals globals
    {- add parameters from invocations to incomplete and variadic functions -}
    let iparmods = if close then addParsFromInvokes parmodtmpl else parmodtmpl
    {- Output -}
    putStr $ unpack $ pStringNoColor $ encode iparmods
    
defFilter :: DeclEvent -> Bool
defFilter (DeclEvent (FunctionDef _)) = True
defFilter (DeclEvent (ObjectDef _)) = True
defFilter _ = False

declFilter :: DeclEvent -> Bool
declFilter (DeclEvent (Declaration _)) = True
declFilter (TagEvent (CompDef _)) = True
declFilter _ = False
