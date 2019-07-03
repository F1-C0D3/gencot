{-# LANGUAGE PackageImports #-}
module Main where

import System.Environment (getArgs)
import Text.JSON (encode)
import Text.Pretty.Simple (pStringNoColor)
import Data.Text.Lazy (unpack)
import Control.Monad (when)

import Language.C.Analysis
import Language.C.Analysis.DefTable (globalDefs)

import Gencot.Input (readFromInput_,getDeclEvents,getOwnDeclEvents)
import Gencot.Util.CallGraph (getCallGraph,runCTrav)
import Gencot.Json.Translate (transGlobals)
import Gencot.Json.Process (addParsFromInvokes)
import Gencot.Traversal (runWithTable)

main :: IO ()
main = do
    {- get and test arguments -}
    args <- getArgs
    when (null args || length args > 2) $ error "expected arguments: <original source file name> close?"
    {- parse and analyse C source and get global definitions -}
    table <- readFromInput_
    {- get input file name -}
    let fnam = head args
    {- test for close option -}
    let close = (length args) > 1
    {- convert symbol table to list of constructs to be processed -}
    let globals = if close
                    then getDeclEvents (globalDefs table) declFilter
                    else getOwnDeclEvents (globalDefs table) defFilter
    {- get call graph -}
    cg <- getCallGraph table globals
    {- translate functions to Json parmod description -}
    parmods <- runCTrav cg table fnam $ transGlobals globals
    {- add parameters from invocations to incomplete and variadic functions -}
    let iparmods = if close then addParsFromInvokes parmods else parmods
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
