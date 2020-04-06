{-# LANGUAGE PackageImports, TypeSynonymInstances, FlexibleInstances #-}
module Gencot.Traversal where

import Control.Monad (liftM)
import Data.Map (Map,findWithDefault,empty)

import Language.C.Analysis.DefTable (DefTable)
import Language.C.Data.Ident (SUERef,Ident,identToString)
import Language.C.Analysis.TravMonad (Trav,runTrav,travErrors,withDefTable,getUserState,modifyUserState)

import Gencot.Input (showWarnings,errorOnLeft)
import Gencot.Names (FileNameTrav,getFileName)
import Gencot.Items.Properties (ItemProperties)

-- | The traversal state for processing C code.
-- The first component is the name of the C source file, or "" if several source files are processed
-- The second component is the set of translated nested tag definitions
-- The third component is the item property map from item ids to property string lists
-- The fourth component is the list of type names where to stop resolving external types together with a flag whether to use the list
type FTrav = Trav (String,[SUERef],ItemProperties,(Bool,[String]))

runFTrav :: DefTable -> (String,ItemProperties,(Bool,[String])) -> FTrav a -> IO a
runFTrav table (f,ipm,tds) action = do
    (res,state) <- errorOnLeft "Error during translation" $ 
        runTrav (f,[],ipm,tds) $ (withDefTable $ const ((),table)) >> action
    showWarnings $ travErrors state
    return res
    
runWithTable :: DefTable -> FTrav a -> IO a
runWithTable table action = runFTrav table ("",empty,(False,[])) action

instance FileNameTrav FTrav where
    getFileName = do
        (f,_,_,_) <- getUserState 
        return f

markTagAsNested :: SUERef -> FTrav ()
markTagAsNested ref = modifyUserState (\(s,ntl,spl,tds) -> (s,ref : ntl,spl,tds))

isMarkedAsNested :: SUERef -> FTrav Bool
isMarkedAsNested ref = do
    (_,ntl,_,_) <- getUserState
    return $ elem ref ntl

getProperties :: String -> FTrav [String]
getProperties iid = do
    (_,_,ipm,_) <- getUserState
    return $ findWithDefault [] iid ipm

hasProperty :: String -> String -> FTrav Bool
hasProperty prop iid = do
    (_,_,ipm,_) <- getUserState
    return $ elem prop $ findWithDefault [] iid ipm
    
class (Monad m) => TypeNamesTrav m where
    stopResolvTypeName :: Ident -> m Bool

instance TypeNamesTrav FTrav where
    stopResolvTypeName idnam = do
        (_,_,_,tds) <- getUserState
        if fst tds then return $ elem (identToString idnam) $ snd tds
                   else return True
