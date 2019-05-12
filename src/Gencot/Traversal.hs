{-# LANGUAGE PackageImports #-}
module Gencot.Traversal where

import System.Environment (getArgs)

import Language.C.Analysis.DefTable (DefTable)
import Language.C.Analysis.TravMonad (Trav,runTrav,travErrors,withDefTable)

import Gencot.Input (showWarnings,errorOnLeft)

type FTrav = Trav String

runFTrav :: FTrav a -> IO a
runFTrav action = do
    (res,state) <- errorOnLeft "Error during translation" $ runTrav "" action
    showWarnings $ travErrors state
    return res
    
runWithTable :: DefTable -> FTrav a -> IO a
runWithTable table action = do
    args <- getArgs
    fnam <- if null args 
               then error "Error: Source file name expected as argument" 
               else return $ head args
    (res,state) <- errorOnLeft "Error during translation" $ 
        runTrav fnam $ (withDefTable $ const ((),table)) >> action
    showWarnings $ travErrors state
    return res

