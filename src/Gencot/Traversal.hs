{-# LANGUAGE PackageImports, TypeSynonymInstances, FlexibleInstances #-}
module Gencot.Traversal where

import Control.Monad (liftM)
import Data.Map (Map,findWithDefault,empty)

import Language.C.Analysis.DefTable (DefTable)
import Language.C.Data.Ident (SUERef)
import Language.C.Analysis.TravMonad (Trav,runTrav,travErrors,withDefTable,getUserState,modifyUserState)

import Gencot.Input (showWarnings,errorOnLeft)
import Gencot.Names (FileNameTrav,getFileName)

-- | Simplified form of evaluated function description sequence.
-- A mapping from function identifiers to sequences of parameter description values.
-- For every parameter the description is one of "yes", "discarded", "no", "nonlinear", "result", or "readonly".
type ParmodMap = Map String [String]

-- | The traversal state for processing C code.
-- The first component is the name of the C source file, or "" if several source files are processed
-- The second component is the parameter modification description.
-- The third component is the set of translated nested tag definitions
-- The fourth component is the list of safe pointers which are never NULL
type FTrav = Trav (String,ParmodMap,[SUERef],[String])

runFTrav :: DefTable -> (String,ParmodMap,[String]) -> FTrav a -> IO a
runFTrav table (f,p,spl) action = do
    (res,state) <- errorOnLeft "Error during translation" $ 
        runTrav (f,p,[],spl) $ (withDefTable $ const ((),table)) >> action
    showWarnings $ travErrors state
    return res
    
runWithTable :: DefTable -> FTrav a -> IO a
runWithTable table action = runFTrav table ("",empty,[]) action

instance FileNameTrav FTrav where
    getFileName = do
        (f,_,_,_) <- getUserState 
        return f

getParmods :: String -> FTrav [String]
getParmods fid = do
    (_,p,_,_) <- getUserState 
    return $ findWithDefault [] fid p

markTagAsNested :: SUERef -> FTrav ()
markTagAsNested ref = modifyUserState (\(s,p,ntl,spl) -> (s,p,ref : ntl,spl))

isMarkedAsNested :: SUERef -> FTrav Bool
isMarkedAsNested ref = do
    (_,_,ntl,_) <- getUserState
    return $ elem ref ntl

isSafePointer :: String -> FTrav Bool
isSafePointer pid = do
    (_,_,_,spl) <- getUserState
    return $ elem pid spl
    
