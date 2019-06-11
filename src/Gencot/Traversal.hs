{-# LANGUAGE PackageImports, TypeSynonymInstances, FlexibleInstances #-}
module Gencot.Traversal where

import Language.C.Analysis.DefTable (DefTable)
import Language.C.Analysis.TravMonad (Trav,runTrav,travErrors,withDefTable,getUserState)

import Gencot.Input (showWarnings,errorOnLeft)

type FTrav = Trav String

runFTrav :: FTrav a -> IO a
runFTrav action = do
    (res,state) <- errorOnLeft "Error during translation" $ runTrav "" action
    showWarnings $ travErrors state
    return res
    
runWithTable :: DefTable -> String -> FTrav a -> IO a
runWithTable table init action = do
    (res,state) <- errorOnLeft "Error during translation" $ 
        runTrav init $ (withDefTable $ const ((),table)) >> action
    showWarnings $ travErrors state
    return res

class (Monad m) => FileNameTrav m where
    getFileName :: m String

instance FileNameTrav FTrav where
    getFileName = getUserState
