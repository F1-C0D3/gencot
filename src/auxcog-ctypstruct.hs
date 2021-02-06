{-# LANGUAGE PackageImports #-}
module Main where

import Language.C.Analysis
import Language.C.Analysis.DefTable (globalDefs)

import Gencot.Input (readFromInput_,getOwnDeclEvents)
import Gencot.Text.CTypInfo (procStructs)

main :: IO ()
main = do
    {- parse and analyse C source and get global definitions -}
    table <- readFromInput_
    {- translate global declarations and definitions to Cogent -}
    let typinfo = procStructs $ getOwnDeclEvents (globalDefs table) constructFilter
    {- Output -}
    putStrLn $ unlines typinfo

constructFilter :: DeclEvent -> Bool
constructFilter (TagEvent (CompDef (CompType _ StructTag _ _ _))) = True
constructFilter _ = False
