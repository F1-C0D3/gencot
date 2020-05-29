{-# LANGUAGE PackageImports #-}
module Main where

import System.Environment (getArgs)
import Control.Monad (when,liftM)

import Language.C.Data.Ident
import Language.C.Analysis
import Language.C.Analysis.DefTable (globalDefs)

import Gencot.Input (readFromInput_,getOwnDeclEvents)
import Gencot.Items.Properties (readPropertiesFromFile)
import Gencot.Items.Identifier (getTypedefNames)
import Gencot.Traversal (runFTrav)
import Gencot.C.Output (showTopLevels)
import Gencot.C.Generate (genEntries)

main :: IO ()
main = do
    {- get and test arguments -}
    args <- getArgs
    when (length args /= 3) 
        $ error "expected arguments: <original source file name> <item properties file name> <used external items file name>"
    {- get own file name -}
    let fnam = head args
    {- get item property map -}
    ipm <- readPropertiesFromFile $ head $ tail args
    {- get list of additional external items to process -}
    useditems <- (liftM ((filter (not . null)) . lines)) (readFile $ head $ tail $ tail args)
    {- parse and analyse C source and get global definitions -}
    table <- readFromInput_
    {- Determine type names used directly in the Cogent compilation unit -}
    let unitTypeNames = getTypedefNames useditems
    {- translate global declarations and definitions to Cogent -}
    wrappers <- runFTrav table (fnam,ipm,(True,unitTypeNames)) $ genEntries $ getOwnDeclEvents (globalDefs table) constructFilter
    {- Output -}
    putStrLn $ showTopLevels wrappers

constructFilter :: DeclEvent -> Bool
constructFilter (DeclEvent fdef@(FunctionDef _)) | declLinkage fdef == ExternalLinkage = True
constructFilter _ = False

