{-# LANGUAGE PackageImports #-}
module Main where

import System.Environment (getArgs)
import Control.Monad (when)
import Data.Map (empty)

import Language.C.Analysis
import Language.C.Analysis.DefTable (globalDefs)

import Gencot.Input (readFromInput_,getOwnDeclEvents)
import Gencot.Text.Decls (transDecls)
import Gencot.Names (readNameMapFromFile)
import Gencot.Traversal (runFTrav)

main :: IO ()
main = do
    {- get arguments -}
    args <- getArgs
    when (length args /= 1) 
        $ error "expected arguments: <name prefix map>"
    {- get name prefix map -}
    npm <- readNameMapFromFile $ head args
    table <- readFromInput_
    out <- runFTrav table ("", npm, empty,(False,[])) $ transDecls $ getOwnDeclEvents (globalDefs table) declFilter
    putStrLn $ unlines out

declFilter :: DeclEvent -> Bool
declFilter (DeclEvent (Declaration (Decl (VarDecl _ (DeclAttrs _ (FunLinkage ExternalLinkage) _) _) _))) = True
declFilter (DeclEvent (Declaration (Decl (VarDecl _ (DeclAttrs _ (Static ExternalLinkage _) _) _) _))) = True
declFilter _ = False
