{-# LANGUAGE PackageImports, TypeSynonymInstances, FlexibleInstances #-}
module Gencot.Traversal where

import Control.Monad (liftM)
import Data.Map as M (Map,findWithDefault,empty,keys,filterWithKey,insert,lookup)
import Data.Functor.Identity (Identity)

import Language.C.Analysis.DefTable (DefTable)
import Language.C.Data.Ident (SUERef,Ident,identToString)
import Language.C.Analysis.TravMonad (TravT,runTrav,travErrors,withDefTable,getUserState,modifyUserState,getDefTable)
import Language.C.Analysis.SemRep (IdentDecl)

import Gencot.Input (showWarnings,errorOnLeft)
import Gencot.Names (FileNameTrav,getFileName,NamePrefixMap,lookupPrefix,MapNamesTrav,matchPrefix)
import Gencot.Items.Properties (ItemProperties)

-- | Table for looking up item ids of local variables and parameters.
-- The first component is a stack of contexts mapping C identifiers to item ids.
-- The second component maps C variable names to their next number to be used for the id of a local variable with this name.
type LocalItemIdTable = ([Map String String],Map String Int)

-- | Map from item ids to declarations/definitions for global variables.
type GlobItemMap = Map String IdentDecl

-- | The traversal state for processing C code.
type FTrav = TravT (String,           -- name of the C source file
                    NamePrefixMap,    -- name prefix map
                    [SUERef],         -- set of translated nested tag definitions
                    ItemProperties,   -- item property map from item ids to property string lists
                    (Bool,[String]),  -- list of type names where to stop resolving external types together with a flag whether to use the list
                    Maybe IdentDecl,  -- definition of the current function while traversing a function body
                    LocalItemIdTable, -- table of local item ids while traversing a function body
                    (Int,Int),        -- pair of counters for Cogent value and component variables
                    GlobItemMap,      -- map from global item ids to their declarations/definitions
                    String)           -- translation configuration string
                Identity

instance MonadFail FTrav where
  fail = error "FTrav monad failed"

runFTrav :: DefTable -> (String,NamePrefixMap,ItemProperties,(Bool,[String]),GlobItemMap,String) -> FTrav a -> IO a
runFTrav table (f,npm,ipm,tds,gmap,tconf) action = do
    (res,state) <- errorOnLeft "Error during processing" $
        runTrav (f,npm,[],ipm,tds,Nothing,([],empty),(0,0),gmap,tconf) $ (withDefTable $ const ((),table)) >> action
    showWarnings $ travErrors state
    return res
    
runWithTable :: DefTable -> FTrav a -> IO a
runWithTable table action = runFTrav table ("",[],empty,(False,[]),empty,"") action

instance FileNameTrav FTrav where
    getFileName = do
        (f,_,_,_,_,_,_,_,_,_) <- getUserState
        return f

instance MapNamesTrav FTrav where
    matchPrefix name = do
        (_,npm,_,_,_,_,_,_,_,_) <- getUserState
        return $ lookupPrefix name npm

markTagAsNested :: SUERef -> FTrav ()
markTagAsNested ref = modifyUserState (\(s,npm,ntl,spl,tds,fdf,idm,cnt,gmap,tconf) -> (s,npm,ref : ntl,spl,tds,fdf,idm,cnt,gmap,tconf))

isMarkedAsNested :: SUERef -> FTrav Bool
isMarkedAsNested ref = do
    (_,_,ntl,_,_,_,_,_,_,_) <- getUserState
    return $ elem ref ntl

getItems :: (String -> [String] -> Bool) -> FTrav [String]
getItems pred = do
    (_,_,_,ipm,_,_,_,_,_,_) <- getUserState
    return $ keys $ filterWithKey pred ipm

getProperties :: String -> FTrav [String]
getProperties iid = do
    (_,_,_,ipm,_,_,_,_,_,_) <- getUserState
    return $ findWithDefault [] iid ipm

hasProperty :: String -> String -> FTrav Bool
hasProperty prop iid = do
    (_,_,_,ipm,_,_,_,_,_,_) <- getUserState
    return $ elem prop $ findWithDefault [] iid ipm
    
class (Monad m) => TypeNamesTrav m where
    stopResolvTypeName :: Ident -> m Bool

instance TypeNamesTrav FTrav where
    stopResolvTypeName idnam = do
        (_,_,_,_,tds,_,_,_,_,_) <- getUserState
        if fst tds then return $ elem (identToString idnam) $ snd tds
                   else return True
    
getFunDef :: FTrav (Maybe IdentDecl)
getFunDef = do
    (_,_,_,_,_,fdf,_,_,_,_) <- getUserState
    return fdf

setFunDef :: IdentDecl -> FTrav ()
setFunDef fdef = modifyUserState (\(s,npm,ntl,spl,tds,_,idm,cnt,gmap,tconf) -> (s,npm,ntl,spl,tds,Just fdef,idm,cnt,gmap,tconf))

clrFunDef :: FTrav ()
clrFunDef = modifyUserState (\(s,npm,ntl,spl,tds,_,idm,cnt,gmap,tconf) -> (s,npm,ntl,spl,tds,Nothing,idm,cnt,gmap,tconf))

getItemId :: String -> FTrav String
getItemId s = do
    (_,_,_,_,_,_,(ms,_),_,_,_) <- getUserState
    return $ getId s ms
    where getId s [] = ""
          getId s (m : ms) = 
              case M.lookup s m of
                   Nothing -> getId s ms
                   Just iid -> iid

enterItemScope :: FTrav ()
enterItemScope = modifyUserState (\(s,npm,ntl,spl,tds,fdf,(ms,vn),cnt,gmap,tconf) -> (s,npm,ntl,spl,tds,fdf,(empty : ms,vn),cnt,gmap,tconf))

leaveItemScope :: FTrav ()
leaveItemScope = modifyUserState (\(s,npm,ntl,spl,tds,fdf,(ms,vn),cnt,gmap,tconf) -> (s,npm,ntl,spl,tds,fdf,(tail ms,vn),cnt,gmap,tconf))

registerItemId :: String -> String -> FTrav ()
registerItemId s iid = modifyUserState (\(s,npm,ntl,spl,tds,fdf,(ms,vn),cnt,gmap,tconf)
                               -> (s,npm,ntl,spl,tds,fdf,((insert s iid $ head ms) : tail ms,vn),cnt,gmap,tconf))

nextVarNum :: String -> FTrav Int
nextVarNum s = do
    (_,_,_,_,_,_,(_,vn),_,_,_) <- getUserState
    let res = case M.lookup s vn of
                 Nothing -> 1
                 Just v -> v+1
    modifyUserState (\(s,npm,ntl,spl,tds,fdf,(ms,vn),cnt,gmap,tconf) -> (s,npm,ntl,spl,tds,fdf,(ms,insert s res vn),cnt,gmap,tconf))
    return res

resetVarNums :: FTrav ()
resetVarNums = modifyUserState (\(s,npm,ntl,spl,tds,fdf,(ms,vn),cnt,gmap,tconf) -> (s,npm,ntl,spl,tds,fdf,(ms,empty),cnt,gmap,tconf))

resetVarCounters :: FTrav ()
resetVarCounters = modifyUserState (\(s,npm,ntl,spl,tds,fdf,idm,_,gmap,tconf) -> (s,npm,ntl,spl,tds,fdf,idm,(0,0),gmap,tconf))

resetValCounter :: FTrav ()
resetValCounter = modifyUserState (\(s,npm,ntl,spl,tds,fdf,idm,(_,cmp),gmap,tconf) -> (s,npm,ntl,spl,tds,fdf,idm,(0,cmp),gmap,tconf))

getValCounter :: FTrav Int
getValCounter = do
    (_,_,_,_,_,_,_,(val,_),_,_) <- getUserState
    modifyUserState (\(s,npm,ntl,spl,tds,fdf,idm,(_,cmp),gmap,tconf) -> (s,npm,ntl,spl,tds,fdf,idm,(val+1,cmp),gmap,tconf))
    return val

getCmpCounter :: FTrav Int
getCmpCounter = do
    (_,_,_,_,_,_,_,(_,cmp),_,_) <- getUserState
    modifyUserState (\(s,npm,ntl,spl,tds,fdf,idm,(val,_),gmap,tconf) -> (s,npm,ntl,spl,tds,fdf,idm,(val,cmp+1),gmap,tconf))
    return cmp

lookupGlobItem :: String -> FTrav (Maybe IdentDecl)
lookupGlobItem iid = do
    (_,_,_,_,_,_,_,_,gmap,_) <- getUserState
    return $ M.lookup iid gmap

getTConf :: FTrav String
getTConf = do
    (_,_,_,_,_,_,_,_,_,tconf) <- getUserState
    return tconf
