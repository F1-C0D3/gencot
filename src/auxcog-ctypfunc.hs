{-# LANGUAGE PackageImports #-}
module Main where

import Data.List (isPrefixOf)

import Language.C.Data.Ident
import Language.C.Analysis
import Language.C.Analysis.DefTable (globalDefs)

import Gencot.Input (readFromInput_,getOwnDeclEvents)
import Gencot.Text.CTypInfo (procFuncs)

main :: IO ()
main = do
    {- parse and analyse C source and get global definitions -}
    table <- readFromInput_
    {- translate global declarations and definitions to Cogent -}
    let typinfo = procFuncs $ getOwnDeclEvents (globalDefs table) constructFilter
    {- Output -}
    putStrLn $ unlines typinfo

constructFilter :: DeclEvent -> Bool
constructFilter (DeclEvent (FunctionDef (FunDef (VarDecl (VarName (Ident nam _ _) _) _ _) _ _))) = "dispatch_t" `isPrefixOf` nam
constructFilter _ = False
