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

-- | The traversal state for processing C code.
-- The first component is the name of the C source file.idm
-- The second component is the name prefix map.
-- The third component is the set of translated nested tag definitions
-- The fourth component is the item property map from item ids to property string lists
-- The fifth component is the list of type names where to stop resolving external types together with a flag whether to use the list
-- The sixth component is the definition of the current function while traversing a function body
-- The seventh component is the table of local item ids while traversing a function body
-- The eighth component is the pair of counters for Cogent value and component variables
-- The nineth component is the translation configuration string
type FTrav = TravT (String,NamePrefixMap,[SUERef],ItemProperties,(Bool,[String]),Maybe IdentDecl,([Map String String],Map String Int),(Int,Int),String) Identity

instance MonadFail FTrav where
  fail = error "FTrav monad failed"

runFTrav :: DefTable -> (String,NamePrefixMap,ItemProperties,(Bool,[String]),String) -> FTrav a -> IO a
runFTrav table (f,npm,ipm,tds,tconf) action = do
    (res,state) <- errorOnLeft "Error during translation" $ 
        runTrav (f,npm,[],ipm,tds,Nothing,([],empty),(0,0),tconf) $ (withDefTable $ const ((),table)) >> action
    showWarnings $ travErrors state
    return res
    
runWithTable :: DefTable -> FTrav a -> IO a
runWithTable table action = runFTrav table ("",[],empty,(False,[]),"") action

instance FileNameTrav FTrav where
    getFileName = do
        (f,_,_,_,_,_,_,_,_) <- getUserState 
        return f

instance MapNamesTrav FTrav where
    matchPrefix name = do
        (_,npm,_,_,_,_,_,_,_) <- getUserState 
        return $ lookupPrefix name npm

markTagAsNested :: SUERef -> FTrav ()
markTagAsNested ref = modifyUserState (\(s,npm,ntl,spl,tds,fdf,idm,cnt,tconf) -> (s,npm,ref : ntl,spl,tds,fdf,idm,cnt,tconf))

isMarkedAsNested :: SUERef -> FTrav Bool
isMarkedAsNested ref = do
    (_,_,ntl,_,_,_,_,_,_) <- getUserState
    return $ elem ref ntl

getItems :: (String -> [String] -> Bool) -> FTrav [String]
getItems pred = do
    (_,_,_,ipm,_,_,_,_,_) <- getUserState
    return $ keys $ filterWithKey pred ipm

getProperties :: String -> FTrav [String]
getProperties iid = do
    (_,_,_,ipm,_,_,_,_,_) <- getUserState
    return $ findWithDefault [] iid ipm

hasProperty :: String -> String -> FTrav Bool
hasProperty prop iid = do
    (_,_,_,ipm,_,_,_,_,_) <- getUserState
    return $ elem prop $ findWithDefault [] iid ipm
    
class (Monad m) => TypeNamesTrav m where
    stopResolvTypeName :: Ident -> m Bool

instance TypeNamesTrav FTrav where
    stopResolvTypeName idnam = do
        (_,_,_,_,tds,_,_,_,_) <- getUserState
        if fst tds then return $ elem (identToString idnam) $ snd tds
                   else return True
    
getFunDef :: FTrav (Maybe IdentDecl)
getFunDef = do
    (_,_,_,_,_,fdf,_,_,_) <- getUserState
    return fdf

setFunDef :: IdentDecl -> FTrav ()
setFunDef fdef = modifyUserState (\(s,npm,ntl,spl,tds,_,idm,cnt,tconf) -> (s,npm,ntl,spl,tds,Just fdef,idm,cnt,tconf))

clrFunDef :: FTrav ()
clrFunDef = modifyUserState (\(s,npm,ntl,spl,tds,_,idm,cnt,tconf) -> (s,npm,ntl,spl,tds,Nothing,idm,cnt,tconf))

getItemId :: String -> FTrav String
getItemId s = do
    (_,_,_,_,_,_,(ms,_),_,_) <- getUserState
    return $ getId s ms
    where getId s [] = ""
          getId s (m : ms) = 
              case M.lookup s m of
                   Nothing -> getId s ms
                   Just iid -> iid

enterItemScope :: FTrav ()
enterItemScope = modifyUserState (\(s,npm,ntl,spl,tds,fdf,(ms,vn),cnt,tconf) -> (s,npm,ntl,spl,tds,fdf,(empty : ms,vn),cnt,tconf))

leaveItemScope :: FTrav ()
leaveItemScope = modifyUserState (\(s,npm,ntl,spl,tds,fdf,(ms,vn),cnt,tconf) -> (s,npm,ntl,spl,tds,fdf,(tail ms,vn),cnt,tconf))

registerItemId :: String -> String -> FTrav ()
registerItemId s iid = modifyUserState (\(s,npm,ntl,spl,tds,fdf,(ms,vn),cnt,tconf)
                               -> (s,npm,ntl,spl,tds,fdf,((insert s iid $ head ms) : tail ms,vn),cnt,tconf))

nextVarNum :: String -> FTrav Int
nextVarNum s = do
    (_,_,_,_,_,_,(_,vn),_,_) <- getUserState
    let res = case M.lookup s vn of
                 Nothing -> 1
                 Just v -> v+1
    modifyUserState (\(s,npm,ntl,spl,tds,fdf,(ms,vn),cnt,tconf) -> (s,npm,ntl,spl,tds,fdf,(ms,insert s res vn),cnt,tconf))
    return res

resetVarNums :: FTrav ()
resetVarNums = modifyUserState (\(s,npm,ntl,spl,tds,fdf,(ms,vn),cnt,tconf) -> (s,npm,ntl,spl,tds,fdf,(ms,empty),cnt,tconf))

resetVarCounters :: FTrav ()
resetVarCounters = modifyUserState (\(s,npm,ntl,spl,tds,fdf,idm,_,tconf) -> (s,npm,ntl,spl,tds,fdf,idm,(0,0),tconf))

resetValCounter :: FTrav ()
resetValCounter = modifyUserState (\(s,npm,ntl,spl,tds,fdf,idm,(_,cmp),tconf) -> (s,npm,ntl,spl,tds,fdf,idm,(0,cmp),tconf))

getValCounter :: FTrav Int
getValCounter = do
    (_,_,_,_,_,_,_,(val,_),_) <- getUserState
    modifyUserState (\(s,npm,ntl,spl,tds,fdf,idm,(_,cmp),tconf) -> (s,npm,ntl,spl,tds,fdf,idm,(val+1,cmp),tconf))
    return val

getCmpCounter :: FTrav Int
getCmpCounter = do
    (_,_,_,_,_,_,_,(_,cmp),_) <- getUserState
    modifyUserState (\(s,npm,ntl,spl,tds,fdf,idm,(val,_),tconf) -> (s,npm,ntl,spl,tds,fdf,idm,(val,cmp+1),tconf))
    return cmp

getTConf :: FTrav String
getTConf = do
    (_,_,_,_,_,_,_,_,tconf) <- getUserState
    return tconf
