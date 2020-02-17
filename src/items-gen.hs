{-# LANGUAGE PackageImports #-}
module Main where

import System.Environment (getArgs)
import Control.Monad (when)
import Data.Map (empty)

import Language.C.Analysis
import Language.C.Data.Ident (isAnonymousRef)
import Language.C.Analysis.DefTable (globalDefs)

import Gencot.Input (readFromInput_,getOwnDeclEvents)
import Gencot.Items.Translate (transGlobals)
import Gencot.Items.Properties (showProperties)
import Gencot.Traversal (runFTrav)

main :: IO ()
main = do
    {- get and test arguments -}
    args <- getArgs
    when (null args || length args > 1) $ error "expected arguments: <original source file name>"
    {- parse and analyse C source and get global definitions -}
    table <- readFromInput_
    {- get input file name -}
    let fnam = head args
    {- determine default properties for all items in globals -}
    ipm <- runFTrav table (fnam,empty,empty,[]) $ transGlobals [] $ getOwnDeclEvents (globalDefs table) defFilter
    {- Output -}
    putStrLn $ showProperties ipm

    
defFilter :: DeclEvent -> Bool
defFilter (DeclEvent (FunctionDef _)) = True
defFilter (DeclEvent (ObjectDef _)) = True
defFilter (TagEvent cd@(CompDef _)) = not $ isAnonymousRef $ sueRef cd
defFilter (TypeDefEvent _) = True
defFilter _ = False

