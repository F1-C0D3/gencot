{-# LANGUAGE PackageImports, TypeSynonymInstances, FlexibleInstances #-}
module Gencot.Traversal where

import Control.Monad (liftM)
import Data.Map (Map,findWithDefault,empty,keys,filterWithKey)
import Data.Functor.Identity (Identity)

import Language.C.Analysis.DefTable (DefTable)
import Language.C.Data.Ident (SUERef,Ident,identToString)
import Language.C.Analysis.TravMonad (TravT,runTrav,travErrors,withDefTable,getUserState,modifyUserState,getDefTable)
import Language.C.Analysis.SemRep (FunDef)

import Gencot.Input (showWarnings,errorOnLeft)
import Gencot.Names (FileNameTrav,getFileName,NamePrefixMap,lookupPrefix,MapNamesTrav,matchPrefix)
import Gencot.Items.Properties (ItemProperties)

-- | The traversal state for processing C code.
-- The first component is the name of the C source file.
-- The second component is the name prefix map.
-- The third component is the set of translated nested tag definitions
-- The fourth component is the item property map from item ids to property string lists
-- The fifth component is the list of type names where to stop resolving external types together with a flag whether to use the list
-- The sixth component is the definition of the current function while traversing a function body
-- The seventh component is the pair of counters for Cogent value and component variables
type FTrav = TravT (String,NamePrefixMap,[SUERef],ItemProperties,(Bool,[String]),Maybe FunDef,(Int,Int)) Identity

instance MonadFail FTrav where
  fail = error "FTrav monad failed"

runFTrav :: DefTable -> (String,NamePrefixMap,ItemProperties,(Bool,[String])) -> FTrav a -> IO a
runFTrav table (f,npm,ipm,tds) action = do
    (res,state) <- errorOnLeft "Error during translation" $ 
        runTrav (f,npm,[],ipm,tds,Nothing,(0,0)) $ (withDefTable $ const ((),table)) >> action
    showWarnings $ travErrors state
    return res
    
runWithTable :: DefTable -> FTrav a -> IO a
runWithTable table action = runFTrav table ("",[],empty,(False,[])) action

instance FileNameTrav FTrav where
    getFileName = do
        (f,_,_,_,_,_,_) <- getUserState 
        return f

instance MapNamesTrav FTrav where
    matchPrefix name = do
        (_,npm,_,_,_,_,_) <- getUserState 
        return $ lookupPrefix name npm

markTagAsNested :: SUERef -> FTrav ()
markTagAsNested ref = modifyUserState (\(s,npm,ntl,spl,tds,fdf,cnt) -> (s,npm,ref : ntl,spl,tds,fdf,cnt))

isMarkedAsNested :: SUERef -> FTrav Bool
isMarkedAsNested ref = do
    (_,_,ntl,_,_,_,_) <- getUserState
    return $ elem ref ntl

getItems :: (String -> [String] -> Bool) -> FTrav [String]
getItems pred = do
    (_,_,_,ipm,_,_,_) <- getUserState
    return $ keys $ filterWithKey pred ipm

getProperties :: String -> FTrav [String]
getProperties iid = do
    (_,_,_,ipm,_,_,_) <- getUserState
    return $ findWithDefault [] iid ipm

hasProperty :: String -> String -> FTrav Bool
hasProperty prop iid = do
    (_,_,_,ipm,_,_,_) <- getUserState
    return $ elem prop $ findWithDefault [] iid ipm
    
class (Monad m) => TypeNamesTrav m where
    stopResolvTypeName :: Ident -> m Bool

instance TypeNamesTrav FTrav where
    stopResolvTypeName idnam = do
        (_,_,_,_,tds,_,_) <- getUserState
        if fst tds then return $ elem (identToString idnam) $ snd tds
                   else return True
    
getFunDef :: FTrav (Maybe FunDef)
getFunDef = do
    (_,_,_,_,_,fdf,_) <- getUserState
    return fdf

setFunDef :: FunDef -> FTrav ()
setFunDef fdef = modifyUserState (\(s,npm,ntl,spl,tds,_,cnt) -> (s,npm,ntl,spl,tds,Just fdef,cnt))

clrFunDef :: FTrav ()
clrFunDef = modifyUserState (\(s,npm,ntl,spl,tds,_,cnt) -> (s,npm,ntl,spl,tds,Nothing,cnt))

resetVarCounters :: FTrav ()
resetVarCounters = modifyUserState (\(s,npm,ntl,spl,tds,fdf,_) -> (s,npm,ntl,spl,tds,fdf,(0,0)))

resetValCounter :: FTrav ()
resetValCounter = modifyUserState (\(s,npm,ntl,spl,tds,fdf,(_,cmp)) -> (s,npm,ntl,spl,tds,fdf,(0,cmp)))

getValCounter :: FTrav Int
getValCounter = do
    (_,_,_,_,_,_,(val,_)) <- getUserState
    modifyUserState (\(s,npm,ntl,spl,tds,fdf,(_,cmp)) -> (s,npm,ntl,spl,tds,fdf,(val+1,cmp)))
    return val

getCmpCounter :: FTrav Int
getCmpCounter = do
    (_,_,_,_,_,_,(_,cmp)) <- getUserState
    modifyUserState (\(s,npm,ntl,spl,tds,fdf,(val,_)) -> (s,npm,ntl,spl,tds,fdf,(val,cmp+1)))
    return cmp
