{-# LANGUAGE PackageImports #-}
module Main where

import Language.C.Analysis
import Language.C.Analysis.DefTable (globalDefs)

import Gencot.Input (readFromInput_,getOwnDeclEvents)
import Gencot.Text.Decls (transDecl)

main :: IO ()
main = do
    table <- readFromInput_
    putStrLn $ unlines $ map transDecl $ getOwnDeclEvents (globalDefs table) declFilter

declFilter :: DeclEvent -> Bool
declFilter (DeclEvent (Declaration (Decl (VarDecl _ (DeclAttrs _ (FunLinkage ExternalLinkage) _) _) _))) = True
declFilter (DeclEvent (Declaration (Decl (VarDecl _ (DeclAttrs _ (Static ExternalLinkage _) _) _) _))) = True
declFilter _ = False
