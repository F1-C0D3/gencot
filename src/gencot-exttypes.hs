{-# LANGUAGE PackageImports #-}
module Main where

import Text.PrettyPrint (Doc,render)

import Language.C.Pretty (pretty)
import Language.C.Data.Ident
import Language.C.Analysis
import Language.C.Analysis.DefTable (globalDefs)

import Gencot.Input (readFromInput)
import Gencot.Util.Types (collectUsedTypes,getUsedTypes,transCloseUsedTypes)
import Gencot.Traversal (runWithTable)
import Gencot.Cogent.Translate (genTypeDefs)
import Gencot.Cogent.Output (prettyTopLevels)

main :: IO ()
main = do
    {- parse and analyse C source and get global definitions, collecting all used types -}
    (table,usedTypes) <- readFromInput empty collectUsedTypes
    {- get list of declarations of externally invoked functions -}
    extDecls <- getExtDecls table
    {- get types used as parameter and result types from extDecls -}
    let usedTypes = union usedTypes $ foldl union empty $ map getUsedTypes extDecls
    {- transitively complete used types -}
    let usedTypes = transCloseUsedTypes (globalDefs table) usedTypes
    {- create Cogent type definitions for all used types -}
    toplvs <- runWithTable table $ genTypeDefs $ toList usedTypes
    {- Output -}
    print $ prettyTopLevels toplvs

