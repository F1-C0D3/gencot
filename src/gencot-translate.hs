{-# LANGUAGE PackageImports #-}
module Main where

import Language.C.Data.Ident
import Language.C.Analysis
import Language.C.Analysis.DefTable (globalDefs)

import Gencot.Input (readFromInput_,getOwnDeclEvents,getArgFileName,getParmodFileName)
import Gencot.Json.Parmod (readParmodsFromFile)
import Gencot.Json.Process (convertParmods)
import Gencot.Traversal (runFTrav)
import Gencot.Cogent.Output (prettyTopLevels)
import Gencot.Cogent.Translate (transGlobals)

main :: IO ()
main = do
    table <- readFromInput_
    fnam <- getArgFileName
    pnam <- getParmodFileName
    parmods <- if null pnam then return [] else readParmodsFromFile pnam
    toplvs <- runFTrav table (fnam,convertParmods parmods) $ transGlobals $ getOwnDeclEvents (globalDefs table) constructFilter
    print $ prettyTopLevels toplvs

constructFilter :: DeclEvent -> Bool
constructFilter (TagEvent (EnumDef (EnumType (AnonymousRef _) _ _ _))) = False
constructFilter (DeclEvent (Declaration _)) = False
constructFilter (DeclEvent (ObjectDef _)) = False
constructFilter _ = True
