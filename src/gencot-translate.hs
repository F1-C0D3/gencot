{-# LANGUAGE PackageImports #-}
module Main where

import Language.C.Data.Ident
import Language.C.Analysis

import Gencot.Input (readFromInput,getDeclEvents)
import Gencot.Names (addInputName)
import Gencot.Cogent.Output (prettyTopLevels)
import Gencot.Cogent.Translate (transGlobals)

main :: IO ()
main = do
    globals <- readFromInput
    globals <- addInputName globals
    print $ prettyTopLevels $ transGlobals globals $ getDeclEvents globals constructFilter

constructFilter :: DeclEvent -> Bool
constructFilter (TagEvent (EnumDef (EnumType (AnonymousRef _) _ _ _))) = False
constructFilter (DeclEvent (Declaration _)) = False
constructFilter (DeclEvent (ObjectDef _)) = False
constructFilter _ = True

