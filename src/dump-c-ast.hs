{-# LANGUAGE PackageImports #-}
module Main where

import Language.C.Data.Ident
import Language.C.Analysis
import Language.C.Analysis.DefTable (globalDefs)

import Gencot.Input (readFromInput_,getOwnDeclEvents)
import Gencot.Text.DumpCAst (dumpGlobals)

main :: IO ()
main = do
    {- parse and analyse C source and get global definitions -}
    table <- readFromInput_
    {- dump global declarations and definitions -}
    let lines = dumpGlobals $ getOwnDeclEvents (globalDefs table) constructFilter
    {- Output -}
    putStrLn $ unlines lines

constructFilter :: DeclEvent -> Bool
constructFilter _ = True
 
