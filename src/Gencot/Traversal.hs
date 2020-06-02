{-# LANGUAGE PackageImports, TypeSynonymInstances, FlexibleInstances #-}
module Gencot.Traversal where

import Control.Monad (liftM)
import Data.Map (Map,findWithDefault,empty)

import Language.C.Analysis.DefTable (DefTable)
import Language.C.Data.Ident (SUERef,Ident,identToString)
import Language.C.Analysis.TravMonad (Trav,runTrav,travErrors,withDefTable,getUserState,modifyUserState,getDefTable)

import Gencot.Input (showWarnings,errorOnLeft)
import Gencot.Names (FileNameTrav,getFileName,NamePrefixMap,lookupPrefix,MapNamesTrav,matchPrefix)
import Gencot.Items.Properties (ItemProperties)

-- | The traversal state for processing C code.
-- The first component is the name of the C source file.
-- The second component is the name prefix map.
-- The third component is the set of translated nested tag definitions
-- The fourth component is the item property map from item ids to property string lists
-- The fifth component is the list of type names where to stop resolving external types together with a flag whether to use the list
type FTrav = Trav (String,NamePrefixMap,[SUERef],ItemProperties,(Bool,[String]))

runFTrav :: DefTable -> (String,NamePrefixMap,ItemProperties,(Bool,[String])) -> FTrav a -> IO a
runFTrav table (f,npm,ipm,tds) action = do
    (res,state) <- errorOnLeft "Error during translation" $ 
        runTrav (f,npm,[],ipm,tds) $ (withDefTable $ const ((),table)) >> action
    showWarnings $ travErrors state
    return res
    
runWithTable :: DefTable -> FTrav a -> IO a
runWithTable table action = runFTrav table ("",[],empty,(False,[])) action

instance FileNameTrav FTrav where
    getFileName = do
        (f,_,_,_,_) <- getUserState 
        return f

instance MapNamesTrav FTrav where
    matchPrefix name = do
        (_,npm,_,_,_) <- getUserState 
        return $ lookupPrefix name npm

markTagAsNested :: SUERef -> FTrav ()
markTagAsNested ref = modifyUserState (\(s,npm,ntl,spl,tds) -> (s,npm,ref : ntl,spl,tds))

isMarkedAsNested :: SUERef -> FTrav Bool
isMarkedAsNested ref = do
    (_,_,ntl,_,_) <- getUserState
    return $ elem ref ntl

getProperties :: String -> FTrav [String]
getProperties iid = do
    (_,_,_,ipm,_) <- getUserState
    return $ findWithDefault [] iid ipm

hasProperty :: String -> String -> FTrav Bool
hasProperty prop iid = do
    (_,_,_,ipm,_) <- getUserState
    return $ elem prop $ findWithDefault [] iid ipm
    
class (Monad m) => TypeNamesTrav m where
    stopResolvTypeName :: Ident -> m Bool

instance TypeNamesTrav FTrav where
    stopResolvTypeName idnam = do
        (_,_,_,_,tds) <- getUserState
        if fst tds then return $ elem (identToString idnam) $ snd tds
                   else return True
    
