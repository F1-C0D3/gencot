{-# LANGUAGE PackageImports #-}
module Main where

import Data.Set (fromList,(\\))

import Language.C.Pretty (pretty)
import Language.C.Data.Ident
import Language.C.Analysis
import Language.C.Analysis.DefTable (globalDefs)

import Gencot.Input (readFromInput_,getDeclEvents)
import Gencot.Traversal (runFTrav)
import Gencot.Util.Invocations (getInvocations)
import Gencot.Util.Ident (getIdents)

main :: IO ()
main = do
    table <- readFromInput_
    let fundefs = getDeclEvents (globalDefs table) constructFilter
    invks <- runFTrav $ getInvocations fundefs
    print $ invks \\ (fromList $ getIdents fundefs)

constructFilter :: DeclEvent -> Bool
constructFilter (DeclEvent (FunctionDef _)) = True
constructFilter _ = False

