{-# LANGUAGE PackageImports, TypeSynonymInstances, FlexibleInstances #-}
module Gencot.Traversal where

import Control.Monad (liftM)

import Language.C.Analysis.DefTable (DefTable)
import Language.C.Analysis.TravMonad (Trav,runTrav,travErrors,withDefTable,getUserState)

import Gencot.Input (showWarnings,errorOnLeft)
import Gencot.Json.Parmod (Parmods)

import Gencot.Names (FileNameTrav,getFileName)

type FTrav = Trav (String,Parmods)

{-
runFTrav :: FTrav a -> IO a
runFTrav action = do
    (res,state) <- errorOnLeft "Error during translation" $ runTrav ("",[]) action
    showWarnings $ travErrors state
    return res
    -}

runFTrav :: DefTable -> (String,Parmods) -> FTrav a -> IO a
runFTrav table init action = do
    (res,state) <- errorOnLeft "Error during translation" $ 
        runTrav init $ (withDefTable $ const ((),table)) >> action
    showWarnings $ travErrors state
    return res
    
runWithTable :: DefTable -> FTrav a -> IO a
runWithTable table action = runFTrav table ("",[]) action

instance FileNameTrav FTrav where
    getFileName = getUserState >>= (return . fst)

getParmods :: FTrav Parmods
getParmods = getUserState >>= (return . snd)
