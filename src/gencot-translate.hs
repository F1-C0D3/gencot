{-# LANGUAGE PackageImports #-}
module Main where

import System.Environment (getArgs)
import Control.Monad (when,liftM)

import Language.C.Data.Ident
import Language.C.Analysis
import Language.C.Analysis.DefTable (globalDefs)

import Gencot.Input (readFromInput_,getOwnDeclEvents)
import Gencot.Items.Properties (readPropertiesFromFile)
import Gencot.Traversal (runFTrav)
import Gencot.Cogent.Output (prettyTopLevels)
import Gencot.Cogent.Translate (transGlobals)

main :: IO ()
main = do
    {- get and test arguments -}
    args <- getArgs
    when (length args /= 2) 
        $ error "expected arguments: <original source file name> <item properties file name>"
    {- get own file name -}
    let fnam = head args
    {- get item property map -}
    ipm <- readPropertiesFromFile $ head $ tail args
    {- parse and analyse C source and get global definitions -}
    table <- readFromInput_
    {- translate global declarations and definitions to Cogent -}
    toplvs <- runFTrav table (fnam,ipm,(False,[])) $ transGlobals $ getOwnDeclEvents (globalDefs table) constructFilter
    {- Output -}
    print $ prettyTopLevels toplvs

constructFilter :: DeclEvent -> Bool
constructFilter (TagEvent (EnumDef (EnumType (AnonymousRef _) _ _ _))) = False
constructFilter (DeclEvent (Declaration _)) = False
constructFilter _ = True
