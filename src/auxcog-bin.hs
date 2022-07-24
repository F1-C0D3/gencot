{-# LANGUAGE PackageImports #-}
module Main where

import System.Environment (getArgs)
import Control.Monad (when,liftM)
import Data.List (isPrefixOf)

import Language.C.Data.Ident
import Language.C.Analysis
import Language.C.Analysis.DefTable (globalDefs)

import Gencot.Input (readFromInput_,getOwnDeclEvents)
import Gencot.Text.CTypInfo (procFuncs,procStructs,readStructsFromFile,readFuntypsFromFile)
import Gencot.Text.Genops (procGenops)

main :: IO ()
main = do
    {- dispatch on component name -}
    args <- getArgs
    when (length args == 0) $ error "auxcog component name expected"
    case head args of
        "ctypfunc" -> auxcogCtypfunc $ tail args
        "ctypstruct" -> auxcogCtypstruct $ tail args
        "genops" -> auxcogGenops $ tail args
        _ -> error $ "Unknown auxcog component: " ++ head args


auxcogCtypfunc :: [String] -> IO ()
auxcogCtypfunc args = do
    {- parse and analyse C source and get global definitions -}
    table <- readFromInput_
    {- translate global declarations and definitions to Cogent -}
    let typinfo = procFuncs $ getOwnDeclEvents (globalDefs table) funcFilter
    {- Output -}
    putStrLn $ unlines typinfo

funcFilter :: DeclEvent -> Bool
funcFilter (DeclEvent (FunctionDef (FunDef (VarDecl (VarName (Ident nam _ _) _) _ _) _ _))) = "dispatch_t" `isPrefixOf` nam
funcFilter _ = False

auxcogCtypstruct :: [String] -> IO ()
auxcogCtypstruct args = do
    {- parse and analyse C source and get global definitions -}
    table <- readFromInput_
    {- translate global declarations and definitions to Cogent -}
    let typinfo = procStructs $ getOwnDeclEvents (globalDefs table) structFilter
    {- Output -}
    putStrLn $ unlines typinfo

structFilter :: DeclEvent -> Bool
structFilter (TagEvent (CompDef (CompType _ StructTag _ _ _))) = True
structFilter _ = False

auxcogGenops :: [String] -> IO ()
auxcogGenops args = do
    {- test command line arguments -}
    when (length args /= 2)
        $ error "expected arguments: <struct types file name> <function types file name>"
    {- read type information from files -}
    structs <- readStructsFromFile (head args)
    funtyps <- readFuntypsFromFile (head (tail args))
    {- process from input to output -}
    inp <- getContents
    putStrLn $ procGenops structs funtyps inp
 
