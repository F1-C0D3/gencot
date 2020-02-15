{-# LANGUAGE PackageImports, TypeSynonymInstances, FlexibleInstances #-}
module Gencot.Util.CallGraph where

import Data.Set as S (Set,empty,union,unions,insert,filter,toList,fromList,map,member,delete)
import Data.Foldable (foldlM,find)
import Control.Monad (liftM,liftM2)

import "language-c" Language.C as LC
import Language.C.Data.Ident as LCI
import Language.C.Data.Node as LCN
import Language.C.Data.Position as LCP
import Language.C.Syntax.AST as LCS
import qualified Language.C.Analysis as LCA
import qualified Language.C.Analysis.DefTable as LCD
import Language.C.Analysis.TravMonad (MonadTrav,Trav,runTrav,travErrors,getUserState)

import Gencot.Names (FileNameTrav,getFileName)
import Gencot.Traversal (FTrav,runWithTable)
import Gencot.Input (showWarnings,errorOnLeft)
import Gencot.Util.Equality
import Gencot.Util.Types (resolveTypedef,getCompType,getMemberDecl)
import Gencot.Util.Expr (getType)
import Gencot.Util.Decl (traverseLocalDecl)

-- | The call graph is the relation between invoking functions and invoked functions.
-- It is represented as the set of all single function invocations.
type CallGraph = Set CGFunInvoke

-- | A function invocation.
-- The first component is the invoking function, the second component is the invoked function.
-- The third component tells whether the invoked function is a locally declared pointer
-- in the invoking function.
type CGFunInvoke = (LCA.FunDef, CGInvoke, Bool)

-- | An invocation description. 
-- It is specified by the invoked function and the number of actual arguments.
-- The invoked function is specified by its declaration (function, function pointer object,
-- function pointer array) or by a struct type and member declaration (function pointer 
-- or function pointer array as struct member).
data CGInvoke =
          IdentInvoke LCA.IdentDecl Int
        | MemberInvoke LCA.CompType LCA.MemberDecl Int

invokeAnum :: CGInvoke -> Int
invokeAnum (IdentInvoke _ i) = i
invokeAnum (MemberInvoke _ _ i) = i

invokeType :: CGInvoke -> LCA.FunType
invokeType cginvk = ftyp $ resolveTypedef $ LCA.declType cginvk
    where ftyp (LCA.FunctionType funtyp _) = funtyp
          ftyp (LCA.PtrType typ _ _) = ftyp $ resolveTypedef typ
          ftyp (LCA.ArrayType typ _ _ _) = ftyp $ resolveTypedef typ

invokeParams :: CGInvoke -> [LCA.ParamDecl]
invokeParams cginvk = case invokeType cginvk of
                           LCA.FunType _ pars _ -> pars
                           LCA.FunTypeIncomplete _ -> []

-- | Retrieve the set of all invoked functions which are specified by an identifier
-- The result contains the declarations of these identifiers.
getIdentInvokes :: CallGraph -> Set LCA.IdentDecl
getIdentInvokes cg = S.map getIdentDecl $ S.filter isIdentInvoke cg

isIdentInvoke :: CGFunInvoke -> Bool
isIdentInvoke (_,IdentInvoke _ _,_) = True
isIdentInvoke _ = False

getIdentDecl :: CGFunInvoke -> LCA.IdentDecl
getIdentDecl (_,IdentInvoke decl _,_) = decl

instance LCN.CNode CGInvoke where
    nodeInfo (IdentInvoke d _) = LCN.nodeInfo d
    nodeInfo (MemberInvoke c d _) = LCN.nodeInfo d

instance LCA.Declaration CGInvoke where
    getVarDecl (IdentInvoke d _) = LCA.getVarDecl d
    getVarDecl (MemberInvoke c d _) = LCA.getVarDecl d

instance Pos CGInvoke where
    posOf (IdentInvoke d _) = posOf d
    posOf (MemberInvoke c d _) = posOf d

instance Eq CGInvoke where
    d1 == d2 = (posOf d1) == (posOf d2)

instance Ord CGInvoke where
    compare d1 d2 = compare (posOf d1) (posOf d2)

getCallGraph :: LCD.DefTable -> [LCA.DeclEvent] -> IO CallGraph
getCallGraph table evs = do
    cg <- runWithTable table $ retrieveCallGraph evs
    return $ S.map (markLocal table) cg

retrieveCallGraph :: MonadTrav m => [LCA.DeclEvent] -> m CallGraph
retrieveCallGraph evs = liftM unions $ mapM retrieveFunInvokes evs

retrieveFunInvokes :: MonadTrav m => LCA.DeclEvent -> m CallGraph
retrieveFunInvokes (LCA.DeclEvent fdef@(LCA.FunctionDef fd)) =
    if (LCA.isNoName nam) 
       then return empty 
       else do 
           hlist <- (liftM toList) $ retrieveInvokes fdef 
           rlist <- mapM (\inv -> return (fd,inv,False)) hlist
           return $ fromList rlist
    where (LCA.VarDecl nam _ _) = LCA.getVarDecl fd
retrieveFunInvokes _ = return empty

markLocal :: LCD.DefTable -> CGFunInvoke -> CGFunInvoke
markLocal table (fd,inv@(IdentInvoke idec _),_) = (fd,inv,isLocal table idec)
markLocal table (fd,inv@(MemberInvoke _ _ _),_) = (fd,inv,False)

isLocal :: LCD.DefTable -> LCA.IdentDecl -> Bool
isLocal table idec = case LCD.lookupIdent (LCA.declIdent idec) table of
                          Just (Right gdec) -> idec /= gdec
                          _ -> True

unionM :: (MonadTrav m, Ord a) => m (Set a) -> m (Set a) -> m (Set a)
unionM = liftM2 union

foldsets :: Ord a => [Set a] -> Set a
foldsets = foldl union empty

class HasInvokes a where
  retrieveInvokes :: MonadTrav m => a -> m (Set CGInvoke)
  mretrieveInvokes :: MonadTrav m => (Maybe a) -> m (Set CGInvoke)
  mretrieveInvokes = maybe (return empty) retrieveInvokes
  
instance HasInvokes a => HasInvokes [a] where
    retrieveInvokes = foldlM accunion empty
        where accunion s el = (liftM (union s)) (retrieveInvokes el)

instance HasInvokes LCA.DeclEvent where
    retrieveInvokes (LCA.DeclEvent idecl) = retrieveInvokes idecl
    retrieveInvokes _ = return empty

instance HasInvokes LCA.IdentDecl where
    retrieveInvokes (LCA.FunctionDef (LCA.FunDef decl stat n)) = do
        LCA.enterFunctionScope
        LCA.defineParams n decl
        res <- retrieveInvokes stat
        LCA.leaveFunctionScope
        return res
    retrieveInvokes _ = return empty

instance HasInvokes LC.CBlockItem where
    retrieveInvokes (LC.CBlockStmt stat) = retrieveInvokes stat
    retrieveInvokes (LC.CBlockDecl decl) =
        traverseLocalDecl decl retrieveInvokes foldsets

instance HasInvokes LC.CDecl where
    retrieveInvokes (LC.CDecl _ dclrs _) = retrieveInvokes dclrs
    retrieveInvokes _ = return empty
    
instance HasInvokes (Maybe LC.CDeclr,Maybe LC.CInit, Maybe LC.CExpr) where
    retrieveInvokes (_,minit,_) = mretrieveInvokes minit

instance HasInvokes LC.CInit where
    retrieveInvokes (LC.CInitExpr expr _) = retrieveInvokes expr
    retrieveInvokes (LC.CInitList ilist _) = retrieveInvokes ilist

instance HasInvokes ([LC.CDesignator],LC.CInit) where
    retrieveInvokes (desigs,cinit) = unionM (retrieveInvokes desigs) (retrieveInvokes cinit)
    
instance HasInvokes LC.CDesignator where
    retrieveInvokes (LC.CArrDesig expr _) = retrieveInvokes expr
    retrieveInvokes (LC.CRangeDesig expr1 expr2 _) = unionM (retrieveInvokes expr1) (retrieveInvokes expr2)

instance HasInvokes LCA.Stmt where
    retrieveInvokes (LC.CExpr mexpr _) = mretrieveInvokes mexpr
    retrieveInvokes (LC.CLabel _ stat _ _) = retrieveInvokes stat
    retrieveInvokes (LC.CCase expr stat _) = unionM (retrieveInvokes expr) (retrieveInvokes stat)
    retrieveInvokes (LC.CDefault stat _) = retrieveInvokes stat
    retrieveInvokes (LC.CCompound _ bis _) = do 
        LCA.enterBlockScope
        bs <- retrieveInvokes bis
        LCA.leaveBlockScope
        return bs
    retrieveInvokes (LC.CIf expr stat mestat _) = 
        unionM (retrieveInvokes expr) 
        $ unionM (retrieveInvokes stat) (mretrieveInvokes mestat)
    retrieveInvokes (LC.CSwitch expr stat _) = unionM (retrieveInvokes expr) (retrieveInvokes stat)
    retrieveInvokes (LC.CWhile expr stat _ _) = unionM (retrieveInvokes expr) (retrieveInvokes stat)
    retrieveInvokes (LC.CFor exdec mcond mstep stat _) = do
        LCA.enterBlockScope
        res <- unionM ((either mretrieveInvokes (\d -> traverseLocalDecl d retrieveInvokes foldsets)) exdec) 
            $ unionM (mretrieveInvokes mcond)
            $ unionM (mretrieveInvokes mstep) (retrieveInvokes stat)
        LCA.leaveBlockScope
        return res
    retrieveInvokes (LC.CReturn mexpr _) = mretrieveInvokes mexpr
    retrieveInvokes _ = return empty
    
instance HasInvokes LC.CExpr where
    retrieveInvokes (LC.CCall expr args _) = do
        a <- unionM (retrieveInvokes expr) (retrieveInvokes args)
        minvk <- getCGInvoke expr $ length args
        case minvk of
             Just invk -> return $ insertMaxArgs invk a
             _ -> return a
    retrieveInvokes (LC.CComma exprs _) = retrieveInvokes exprs
    retrieveInvokes (LC.CAssign _ expr1 expr2 _) = unionM (retrieveInvokes expr1) (retrieveInvokes expr2)
    retrieveInvokes (LC.CCond expr1 mexpr2 expr3 _) = 
        unionM (retrieveInvokes expr1) $ unionM (mretrieveInvokes mexpr2) (retrieveInvokes expr3)
    retrieveInvokes (LC.CBinary _ expr1 expr2 _) = unionM (retrieveInvokes expr1) (retrieveInvokes expr2)
    retrieveInvokes (LC.CCast _ expr _) = retrieveInvokes expr
    retrieveInvokes (LC.CUnary _ expr _) = retrieveInvokes expr
    retrieveInvokes (LC.CIndex expr1 expr2 _) = unionM (retrieveInvokes expr1) (retrieveInvokes expr2)
    retrieveInvokes (LC.CMember expr _ _ _) = retrieveInvokes expr
    retrieveInvokes (LC.CCompoundLit _ ilist _) = retrieveInvokes ilist
    retrieveInvokes (LC.CGenericSelection _ slist a) = retrieveInvokes slist
    retrieveInvokes _ = return empty

instance HasInvokes (Maybe LC.CDecl, CExpr) where
    retrieveInvokes (_,expr) = retrieveInvokes expr

-- | Insert invocation with maximal number of arguments
-- The number of arguments is not respected in CGInvoke equality.
-- Here when inserting an invocation which is already in the set we use the invocation with most arguments.
insertMaxArgs :: CGInvoke -> Set CGInvoke -> Set CGInvoke
insertMaxArgs invk iset =
    if member invk iset 
       then let oinvk = head $ toList $ S.filter (invk ==) iset
            in if invokeAnum invk > invokeAnum oinvk 
                  then insert invk $ delete oinvk iset
                  else iset
       else insert invk iset 

getCGInvoke :: MonadTrav m => LC.CExpr -> Int -> m (Maybe CGInvoke)
getCGInvoke (LC.CVar ident _) alen = do
    mdecl <- LCA.lookupObject ident
    case mdecl of
         Just decl -> return $ Just (IdentInvoke decl alen)
         _ -> return Nothing
getCGInvoke (LC.CMember expr mid pointer _) alen = do
    mtyp <- getType expr
    case mtyp of
         Nothing -> return Nothing
         Just typ -> do
             dt <- LCA.getDefTable
             let ctyp@(LCA.CompType sueref _ _ _ _) = getCompType typ dt
             case getMemberDecl ctyp mid of
                  Nothing -> return Nothing
                  Just mdecl -> if isAnonymousRef sueref 
                                   then return Nothing
                                   else return $ Just (MemberInvoke ctyp mdecl alen)
getCGInvoke (LC.CIndex expr _ _) alen = getCGInvoke expr alen
getCGInvoke (LC.CUnary LC.CIndOp expr _) alen = getCGInvoke expr alen
getCGInvoke _ _ = return Nothing

type CTrav = Trav (String,CallGraph)

runCTrav :: CallGraph -> LCD.DefTable -> String -> CTrav a -> IO a
runCTrav cg table init action = do
    (res,state) <- errorOnLeft "Error during translation" $ 
        runTrav (init,cg) $ (LCA.withDefTable $ const ((),table)) >> action
    showWarnings $ travErrors state
    return res

lookupCallGraph :: LCI.Ident -> CTrav CallGraph
lookupCallGraph idnam = do
    u <- getUserState
    return $ S.filter (\(fd,_,_) -> case LCA.declName fd of {LCA.VarName i _ -> i == idnam; LCA.NoName -> False}) $ snd u

instance FileNameTrav CTrav where
    getFileName = do
        u <- getUserState
        return $ fst u
