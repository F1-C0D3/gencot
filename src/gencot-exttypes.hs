{-# LANGUAGE PackageImports #-}
module Main where

import Text.PrettyPrint (Doc,render)

import Language.C.Pretty (pretty)
import Language.C.Data.Ident
import Language.C.Analysis
import Language.C.Analysis.DefTable (globalDefs)

import Gencot.Input (readFromInput,getDeclEvents)
import Gencot.Traversal (runWithTable)
import Gencot.Cogent.Output (prettyTopLevels)
import Gencot.Cogent.Translate (transGlobals)

main :: IO ()
main = do
    (table,ustate) <- readFromInput [] uhandler
    --toplvs <- runWithTable table $ transGlobals $ getDeclEvents (globalDefs table) constructFilter
    print $ map render $ reverse ustate

uhandler :: DeclEvent -> Trav [Doc] ()
uhandler (TagEvent td) = (modifyUserState ((pretty td) :))
uhandler (DeclEvent dd) = (modifyUserState ((pretty dd) :))
uhandler (ParamEvent pd) = (modifyUserState ((pretty pd) :))
uhandler (LocalEvent ld) = (modifyUserState ((pretty ld) :))
uhandler (TypeDefEvent td) = (modifyUserState ((pretty td) :))
uhandler _ = return ()

constructFilter :: DeclEvent -> Bool
constructFilter (TagEvent (EnumDef (EnumType (AnonymousRef _) _ _ _))) = False
constructFilter (DeclEvent (Declaration _)) = False
constructFilter (DeclEvent (ObjectDef _)) = False
constructFilter _ = True
