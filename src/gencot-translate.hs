{-# LANGUAGE PackageImports #-}
module Main where

import System.Environment (getArgs)
import Control.Monad (when,liftM)
import Data.List (nub)

import Language.C.Data.Ident
import Language.C.Analysis
import Language.C.Analysis.DefTable (globalDefs)

import Gencot.Input (readFromInput_,getOwnDeclEvents)
import Gencot.Json.Parmod (readParmodsFromFile)
import Gencot.Json.Process (convertParmods)
import Gencot.Traversal (runFTrav)
import Gencot.Cogent.Output (prettyTopLevels)
import Gencot.Cogent.Translate (transGlobals)

main :: IO ()
main = do
    {- get and test arguments -}
    args <- getArgs
    when (length args < 2 || length args > 3) 
        $ error "expected arguments: <original source file name> <safe pointer list file name> <parmod description file name>?"
    {- get own file name -}
    let fnam = head args
    {- get list of safe pointers -}
    spl <- (liftM ((filter (not . null)) . lines)) $ readFile $ head $ tail args
    {- get parameter modification descriptions -}
    parmods <- if 3 > length args then return [] else readParmodsFromFile $ head $ tail $ tail args
    {- parse and analyse C source and get global definitions -}
    table <- readFromInput_
    {- translate global declarations and definitions to Cogent -}
    toplvs <- runFTrav table (fnam,convertParmods parmods,nub spl) $ transGlobals $ getOwnDeclEvents (globalDefs table) constructFilter
    {- Output -}
    print $ prettyTopLevels toplvs

constructFilter :: DeclEvent -> Bool
constructFilter (TagEvent (EnumDef (EnumType (AnonymousRef _) _ _ _))) = False
constructFilter (DeclEvent (Declaration _)) = False
constructFilter _ = True
