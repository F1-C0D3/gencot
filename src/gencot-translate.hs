{-# LANGUAGE PackageImports #-}
module Main where

import Language.C.Data.Ident
import Language.C.Analysis
import Language.C.Analysis.DefTable (globalDefs)

import Gencot.Input (readFromInput,getDeclEvents,showWarnings,errorOnLeft)
import Gencot.Names (addInputName)
import Gencot.Cogent.Output (prettyTopLevels)
import Gencot.Cogent.Translate (transGlobals)

main :: IO ()
main = do
    table <- readFromInput
    table <- addInputName table
    (toplvs,warns) <- errorOnLeft "Error in transGlobal" $ 
        runTrav_ $ transGlobals table $ getDeclEvents (globalDefs table) constructFilter
    showWarnings warns
    print $ prettyTopLevels toplvs

constructFilter :: DeclEvent -> Bool
constructFilter (TagEvent (EnumDef (EnumType (AnonymousRef _) _ _ _))) = False
constructFilter (DeclEvent (Declaration _)) = False
constructFilter (DeclEvent (ObjectDef _)) = False
constructFilter _ = True
