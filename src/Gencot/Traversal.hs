{-# LANGUAGE PackageImports, TypeSynonymInstances, FlexibleInstances #-}
module Gencot.Traversal where

import Control.Monad (liftM)
import Data.Map (Map,findWithDefault,empty)

import Language.C.Analysis.DefTable (DefTable)
import Language.C.Data.Ident (SUERef)
import Language.C.Analysis.TravMonad (Trav,runTrav,travErrors,withDefTable,getUserState,modifyUserState)

import Gencot.Input (showWarnings,errorOnLeft)
import Gencot.Names (FileNameTrav,getFileName)

-- | Simplified form of evaluated function descripton sequence.
-- A mapping from function identifiers to sequences of parameter description values.
-- For every parameter the description is one of "yes", "discarded", "no", "nonlinear", "result", or "readonly".
type ParmodMap = Map String [String]

type FTrav = Trav (String,ParmodMap,[SUERef])

runFTrav :: DefTable -> (String,ParmodMap) -> FTrav a -> IO a
runFTrav table (f,p) action = do
    (res,state) <- errorOnLeft "Error during translation" $ 
        runTrav (f,p,[]) $ (withDefTable $ const ((),table)) >> action
    showWarnings $ travErrors state
    return res
    
runWithTable :: DefTable -> FTrav a -> IO a
runWithTable table action = runFTrav table ("",empty) action

instance FileNameTrav FTrav where
    getFileName = do
        (f,_,_) <- getUserState 
        return f

getParmods :: String -> FTrav [String]
getParmods fid = do
    (_,p,_) <- getUserState 
    return $ findWithDefault [] fid p

markTagAsNested :: SUERef -> FTrav ()
markTagAsNested ref = modifyUserState (\(s,p,ntl) -> (s,p,ref : ntl))

isMarkedAsNested :: SUERef -> FTrav Bool
isMarkedAsNested ref = do
    (_,_,ntl) <- getUserState
    return $ elem ref ntl
