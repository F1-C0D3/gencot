{-# LANGUAGE PackageImports, TypeSynonymInstances, FlexibleInstances #-}

-- | Translate C Code to JSON function descriptions.
-- A function description is represented as a JSON object and describes a function or a function pointer. 
-- It mainly consists of a description of the function parameters. 
-- For a function definition, it additionally describes all invocations of functions
-- in the function body.
module Gencot.Json.Translate where

import Data.Set (Set,size,toList,empty,union,fromList,insert,unions,singleton)
import qualified Data.Set as S (filter)
import Data.Maybe (fromJust,catMaybes,mapMaybe)
import Data.List (elemIndex)
import Control.Monad (liftM)
import Data.Foldable (foldlM)
import Text.JSON
import System.FilePath (takeExtension,takeFileName,takeBaseName)

import "language-c" Language.C as LC hiding (pretty,Pretty)
import Language.C.Data.Ident as LCI
import Language.C.Data.Node as LCN
import Language.C.Data.Position as LCP
import Language.C.Analysis as LCA

import Gencot.Util.CallGraph (CallGraph,CGFunInvoke,CGInvoke(IdentInvoke,MemberInvoke),CTrav,lookupCallGraph,invokeAnum,unionM,foldsets,getCGInvoke,invokeType,invokeParams)
import Gencot.Util.Types (isLinearParType,isReadOnlyParType,isFunPointer,isFunction,resolveTypedef,getPointedType,getFunType)
import Gencot.Util.Expr (getRootIdent,isReference)
import Gencot.Util.Decl (traverseLocalDecl)
import Gencot.Names (srcFileName)

qmark = showJSON "?"
jsEmpty = JSArray []

-- | Translate a sequence of C global declarations to a sequence of function descriptions.
transGlobals :: [LCA.DeclEvent] -> CTrav [JSObject JSValue]
transGlobals evs = (liftM concat) $ (mapM transGlobal) evs 

-- | Translate a C global declaration to a sequence of function descriptions.
-- Every function definition is translated to a function description.
-- For each invocation which invokes a local function
-- pointer (a parameter or local variable), a function description for the local function pointer is appended.
-- Every object definition with function pointer type is translated to a function definition.
-- All other global declarations are ignored.
transGlobal :: LCA.DeclEvent -> CTrav [JSObject JSValue]
transGlobal (LCA.DeclEvent (LCA.FunctionDef fdef)) = do
    sfn <- srcFileName fdef
    cg <- (liftM toList) $ lookupCallGraph $ LCA.declIdent fdef
    parmods <- findParModifs fdef
    pardeps <- findParDepnds fdef
    let fpardeps = S.filter (\(decl,_,_,_) -> not $ isin parmods decl) pardeps
    parlist <- mapM (paramEntry parmods fpardeps) $ numberList pars
    tinvokes <- mapM (transInvocation fpardeps sfn) cg
    let invokes = catMaybes tinvokes
    let localcg = filter (\(_,_,loc) -> loc) cg
    locals <- mapM (transLocal sfn) localcg
    return $ [toJSObject ([namEntry (getGlobalNamPrefix fdef sfn) fdef,comEntry,locEntry sfn,nmpEntry ftyp] ++ parlist ++ 
                [nmiEntry invokes] ++ if not (null invokes) && (any maymodify parlist) then [invEntry invokes] else [])] 
        ++ locals
    where (LCA.FunctionType ftyp@(LCA.FunType restype pars isVar) _) = LCA.declType fdef
          maymodify (_,jss) = jss == qmark || jss == showJSON "?depends"
transGlobal (LCA.DeclEvent (LCA.ObjectDef odef)) | isFunPointer $ LCA.declType odef =
    transDecl (getGlobalNamPrefix odef) odef $ getFunType $ getPointedType $ LCA.declType odef
transGlobal (LCA.DeclEvent (LCA.Declaration decl)) | isFunPointer $ LCA.declType decl =
    transDecl (getGlobalNamPrefix decl) decl $ getFunType $ getPointedType $ LCA.declType decl
transGlobal (LCA.DeclEvent (LCA.Declaration decl)) | isFunction $ LCA.declType decl =
    transDecl (getGlobalNamPrefix decl) decl $ getFunType $ LCA.declType decl
transGlobal (LCA.TagEvent (LCA.CompDef (LCA.CompType (LCI.NamedRef cid) _ mdecls _ _))) =
    mapMaybeM (transMember cid) mdecls
    where mapMaybeM :: Monad m => (a -> m (Maybe b)) -> [a] -> m [b]
          mapMaybeM f = liftM catMaybes . mapM f
transGlobal _ = return $ []

-- | Translate a declaration of a function or function pointer to a sequence (of length 1) of function descriptions.
-- getPrefix must be a function which returns the function name prefix when applied to the source file name.
transDecl :: (CNode d,Declaration d) => (String -> String) -> d -> LCA.FunType -> CTrav [JSObject JSValue]
transDecl getPrefix decl ftyp@(LCA.FunType _ pars isVar) = do
    sfn <- srcFileName decl
    parlist <- mapM simpleParamEntry $ numberList pars
    return $ [toJSObject ([namEntry (getPrefix sfn) decl,comEntry,locEntry sfn,nmpEntry ftyp] ++ parlist)] 
transDecl getPrefix decl ftyp@(LCA.FunTypeIncomplete _) = do
    sfn <- srcFileName decl
    return $ [toJSObject ([namEntry (getPrefix sfn) decl,comEntry,locEntry sfn,nmpEntry ftyp])] 

-- | Translate a struct or union member to a function description, if it is a function pointer.
transMember :: LCI.Ident -> LCA.MemberDecl -> CTrav (Maybe (JSObject JSValue))
transMember cid mdecl | isFunPointer $ LCA.declType mdecl =
    liftM (Just . head) $ transDecl (const (getGlobalMemberPrefix cid mdecl)) mdecl 
        $ getFunType $ getPointedType $ LCA.declType mdecl
transMember _ _ = return Nothing

-- | Translate an invocation of a local function pointer to a function description.
transLocal :: String -> CGFunInvoke -> CTrav (JSObject JSValue)
transLocal sfn fi@(fd,invk,_) = do
    parlist <- mapM simpleParamEntry $ numberList $ invokeParams invk
    return $ toJSObject $ [namEntry (getNamPrefix fi sfn) invk,comEntry,locEntry sfn,nmpEntry $ invokeType invk] ++ parlist

-- | Find parameter modifications in a function definition.
-- A parameter modification is an assignment to memory referenced by a (part of a) parameter.
-- The result is the set of parameter object definitions in the function scope of all
-- parameters modified in this way. 
findParModifs :: LCA.FunDef -> CTrav (Set LCA.IdentDecl)
findParModifs (LCA.FunDef decl stat n) = do
    LCA.enterFunctionScope
    LCA.defineParams n decl
    pars <- getParamObjs $ LCA.declType decl
    res <- findParMods pars stat
    LCA.leaveFunctionScope
    return res

-- | Representation of a parameter dependency. 
-- A parameter dependency consists of a (part of a) parameter being passed as argument to a function invocation.
-- It is represented by the parameter object definition in the function scope, the parameter number (starting with 1),
-- the invocation description, and the position of the invocation's argument (starting with 1).
type ParDep = (LCA.IdentDecl,Int,CGInvoke,Int) -- (parameter object def, parameter number, invocation, invocation argument position)

-- | Find parameter dependencies in a function definition.
findParDepnds :: LCA.FunDef -> CTrav (Set ParDep)
findParDepnds (LCA.FunDef decl stat n) = do
    LCA.enterFunctionScope
    LCA.defineParams n decl
    pars <- getParamObjs $ LCA.declType decl
    res <- findParDeps pars stat
    LCA.leaveFunctionScope
    return res

-- | Get all parameter object definitions in the function scope. 
-- The argument is the type of the function, it must include all parameter names.
-- The result is the set of pairs (i,d) where i is the parameter number (starting with 1) and d is the object definition.
getParamObjs :: MonadTrav m => LCA.Type -> m (Set (Int,LCA.IdentDecl))
getParamObjs (LCA.FunctionType (LCA.FunType _ pdecls _) _) = do
    h <- mapM (lookupObject . LCA.declIdent) pdecls
    return $ fromList $ catMaybes $ maybeNumberList h
getParamObjs _ = return empty

-- | Class of C AST nodes which support retrieving parameter modifications and parameter dependencies.
class HasParMods a where
    -- | Find parameter modifications. 
    -- The first argument is the set of all parameters, as returned by 'getParamObjs'.
    findParMods :: MonadTrav m => (Set (Int,LCA.IdentDecl)) -> a -> m (Set LCA.IdentDecl)
    -- | Find parameter modifications for an optional C AST node.
    mfindParMods :: MonadTrav m => (Set (Int,LCA.IdentDecl)) -> (Maybe a) -> m (Set LCA.IdentDecl)
    mfindParMods p = maybe (return empty) (findParMods p)
    -- | Find parameter dependencies. 
    -- The first argument is the set of all parameters, as returned by 'getParamObjs'.
    findParDeps :: MonadTrav m => (Set (Int,LCA.IdentDecl)) -> a -> m (Set ParDep)
    -- | Find parameter dependencies for an optional C AST node.
    mfindParDeps :: MonadTrav m => (Set (Int,LCA.IdentDecl)) -> (Maybe a) -> m (Set ParDep)
    mfindParDeps p = maybe (return empty) (findParDeps p)

instance HasParMods a => HasParMods [a] where
    findParMods p = foldlM accunion empty
        where accunion s el = (liftM (union s)) (findParMods p el)
              
    findParDeps p = foldlM accunion empty
        where accunion s el = (liftM (union s)) (findParDeps p el)

instance HasParMods LC.CBlockItem where
    findParMods p (LC.CBlockStmt stat) = findParMods p stat
    findParMods p (LC.CBlockDecl decl) = 
        traverseLocalDecl decl (findParMods p) foldsets
        
    findParDeps p (LC.CBlockStmt stat) = findParDeps p stat
    findParDeps p (LC.CBlockDecl decl) =
        traverseLocalDecl decl (findParDeps p) foldsets
    
instance HasParMods LC.CDecl where
    findParMods p (LC.CDecl _ dclrs _) = findParMods p dclrs
    findParMods _ _ = return empty

    findParDeps p (LC.CDecl _ dclrs _) = findParDeps p dclrs
    findParDeps _ _ = return empty
    
instance HasParMods (Maybe LC.CDeclr,Maybe LC.CInit, Maybe LC.CExpr) where
    findParMods p (_,minit,_) = mfindParMods p minit

    findParDeps p (_,minit,_) = mfindParDeps p minit

instance HasParMods LC.CInit where
    findParMods p (LC.CInitExpr expr _) = findParMods p expr
    findParMods p (LC.CInitList ilist _) = findParMods p ilist

    findParDeps p (LC.CInitExpr expr _) = findParDeps p expr
    findParDeps p (LC.CInitList ilist _) = findParDeps p ilist

instance HasParMods ([LC.CDesignator],LC.CInit) where
    findParMods p (desigs,cinit) = unionM (findParMods p desigs) (findParMods p cinit)

    findParDeps p (desigs,cinit) = unionM (findParDeps p desigs) (findParDeps p cinit)
    
instance HasParMods LC.CDesignator where
    findParMods p (LC.CArrDesig expr _) = findParMods p expr
    findParMods p (LC.CRangeDesig expr1 expr2 _) = unionM (findParMods p expr1) (findParMods p expr2)

    findParDeps p (LC.CArrDesig expr _) = findParDeps p expr
    findParDeps p (LC.CRangeDesig expr1 expr2 _) = unionM (findParDeps p expr1) (findParDeps p expr2)

instance HasParMods LCA.Stmt where
    findParMods p (LC.CExpr mexpr _) = mfindParMods p mexpr
    findParMods p (LC.CLabel _ stat _ _) = findParMods p stat
    findParMods p (LC.CCase expr stat _) = unionM (findParMods p expr) (findParMods p stat)
    findParMods p (LC.CDefault stat _) = findParMods p stat
    findParMods p (LC.CCompound _ bis _) = do 
        LCA.enterBlockScope
        bs <- findParMods p bis
        LCA.leaveBlockScope
        return bs
    findParMods p (LC.CIf expr stat mestat _) = 
        unionM (findParMods p expr) 
        $ unionM (findParMods p stat) (mfindParMods p mestat)
    findParMods p (LC.CSwitch expr stat _) = unionM (findParMods p expr) (findParMods p stat)
    findParMods p (LC.CWhile expr stat _ _) = unionM (findParMods p expr) (findParMods p stat)
    findParMods p (LC.CFor exdec mcond mstep stat _) = do
        LCA.enterBlockScope
        res <- unionM ((either (mfindParMods p) (\d -> traverseLocalDecl d (findParMods p) foldsets)) exdec) 
            $ unionM (mfindParMods p mcond)
            $ unionM (mfindParMods p mstep) (findParMods p stat)
        LCA.leaveBlockScope
        return res
    findParMods p (LC.CReturn mexpr _) = mfindParMods p mexpr
    findParMods _ _ = return empty
    
    findParDeps p (LC.CExpr mexpr _) = mfindParDeps p mexpr
    findParDeps p (LC.CLabel _ stat _ _) = findParDeps p stat
    findParDeps p (LC.CCase expr stat _) = unionM (findParDeps p expr) (findParDeps p stat)
    findParDeps p (LC.CDefault stat _) = findParDeps p stat
    findParDeps p (LC.CCompound _ bis _) = do 
        LCA.enterBlockScope
        bs <- findParDeps p bis
        LCA.leaveBlockScope
        return bs
    findParDeps p (LC.CIf expr stat mestat _) = 
        unionM (findParDeps p expr) 
        $ unionM (findParDeps p stat) (mfindParDeps p mestat)
    findParDeps p (LC.CSwitch expr stat _) = unionM (findParDeps p expr) (findParDeps p stat)
    findParDeps p (LC.CWhile expr stat _ _) = unionM (findParDeps p expr) (findParDeps p stat)
    findParDeps p (LC.CFor exdec mcond mstep stat _) = do
        LCA.enterBlockScope
        res <- unionM ((either (mfindParDeps p) (\d -> traverseLocalDecl d (findParDeps p) foldsets)) exdec) 
            $ unionM (mfindParDeps p mcond)
            $ unionM (mfindParDeps p mstep) (findParDeps p stat)
        LCA.leaveBlockScope
        return res
    findParDeps p (LC.CReturn mexpr _) = mfindParDeps p mexpr
    findParDeps _ _ = return empty
    
instance HasParMods LC.CExpr where
    findParMods p (LC.CAssign _ lexpr expr _) = do
        res <- unionM (findParMods p lexpr) (findParMods p expr)
        let mlroot = getRootIdent lexpr
        case mlroot of
             Nothing -> return res
             Just lroot -> do
                 mldec <- LCA.lookupObject lroot
                 case mldec of
                      Nothing -> return res
                      Just ldec -> if any (\(_,idec) -> LCA.declIdent idec == LCA.declIdent ldec) p
                                      && isReference lexpr
                                      then return $ insert ldec res 
                                      else return res
    findParMods p (LC.CCall expr args _) = unionM (findParMods p expr) (findParMods p args)
    findParMods p (LC.CComma exprs _) = findParMods p exprs
    findParMods p (LC.CCond expr1 mexpr2 expr3 _) = 
        unionM (findParMods p expr1) $ unionM (mfindParMods p mexpr2) (findParMods p expr3)
    findParMods p (LC.CBinary _ expr1 expr2 _) = unionM (findParMods p expr1) (findParMods p expr2)
    findParMods p (LC.CCast _ expr _) = findParMods p expr
    findParMods p (LC.CUnary _ expr _) = findParMods p expr
    findParMods p (LC.CIndex expr1 expr2 _) = unionM (findParMods p expr1) (findParMods p expr2)
    findParMods p (LC.CMember expr _ _ _) = findParMods p expr
    findParMods p (LC.CCompoundLit _ ilist _) = findParMods p ilist
    findParMods p (LC.CGenericSelection _ slist a) = findParMods p slist
    findParMods _ _ = return empty
    
    findParDeps p (LC.CCall expr args _) = do
        a <- unionM (findParDeps p expr) (findParDeps p args)
        minvk <- getCGInvoke expr $ length args
        case minvk of
             Just invk -> do
                 apd <- liftM unions $ mapM (argParDep p invk) $ numberList args
                 return $ union apd a
             _ -> return a
    findParDeps p (LC.CComma exprs _) = findParDeps p exprs
    findParDeps p (LC.CAssign _ expr1 expr2 _) = unionM (findParDeps p expr1) (findParDeps p expr2)
    findParDeps p (LC.CCond expr1 mexpr2 expr3 _) = 
        unionM (findParDeps p expr1) $ unionM (mfindParDeps p mexpr2) (findParDeps p expr3)
    findParDeps p (LC.CBinary _ expr1 expr2 _) = unionM (findParDeps p expr1) (findParDeps p expr2)
    findParDeps p (LC.CCast _ expr _) = findParDeps p expr
    findParDeps p (LC.CUnary _ expr _) = findParDeps p expr
    findParDeps p (LC.CIndex expr1 expr2 _) = unionM (findParDeps p expr1) (findParDeps p expr2)
    findParDeps p (LC.CMember expr _ _ _) = findParDeps p expr
    findParDeps p (LC.CCompoundLit _ ilist _) = findParDeps p ilist
    findParDeps p (LC.CGenericSelection _ slist a) = findParDeps p slist
    findParDeps _ _ = return empty

instance HasParMods (Maybe LC.CDecl, CExpr) where
    findParMods p (_,expr) = findParMods p expr

    findParDeps p (_,expr) = findParDeps p expr

-- | Find parameter dependencies in a numbered argument of an invocation.
-- The first argument is the set of all parameters, as returned by 'getParamObjs'.
-- The second argument is the invocation description.
-- An invocation argument is a dependency only if the corresponding parameter of the invoked
-- function has a linear type which is not readonly.
argParDep :: MonadTrav m => Set (Int,LCA.IdentDecl) -> CGInvoke -> (Int,LC.CExpr) -> m (Set ParDep)
argParDep p invk (i,expr) = do
    let mroot = getRootIdent expr
    case mroot of
         Nothing -> return empty
         Just root -> do
             madec <- LCA.lookupObject root
             case madec of
                  Nothing -> return empty
                  Just adec -> do
                      let pdecs = S.filter (\(_,d) -> LCA.declIdent d == LCA.declIdent adec) p
                      if null pdecs 
                         then return empty
                         else do
                             let pnum = fst $ head $ toList pdecs
                             if null apars then return $ singleton (adec,pnum,invk,i) 
                             else do
                                 let atyp = LCA.declType ((apars)!!(i-1))
                                 lin <- isLinearParType atyp
                                 if not lin
                                    then return empty
                                    else do
                                        ro <- isReadOnlyParType atyp
                                        if ro then return empty
                                        else return $ singleton (adec,pnum,invk,i) 
    where apars = invokeParams invk

simpleParamEntry :: (Int,LCA.ParamDecl) -> CTrav (String,JSValue)
simpleParamEntry pd = paramEntry empty empty pd

-- | Return a parameter description as a JSON attribute specification (name, value).
-- name is the parameter name as created by 'genParamName'.
-- value is a string: "nonlinear" or "readonly" according to the parameter type; for a parameter which is neither
-- of both, either "yes", if a parameter modification is present, "?depends" if no parameter modification is present
-- but a parameter dependency, and "?" otherwise.
paramEntry :: Set LCA.IdentDecl -> Set ParDep -> (Int,LCA.ParamDecl) -> CTrav (String,JSValue)
paramEntry parmods pardeps pd = do
    lin <- isLinearParType dtyp 
    if lin
       then 
        if isin parmods $ snd pd 
           then return (pn, showJSON "yes")
           else do
               ro <- isReadOnlyParType dtyp
               return (pn, if ro then showJSON "readonly" else if isdep pardeps $ snd pd then showJSON "?depends" else qmark)
       else return (pn, showJSON "nonlinear")
    where dtyp = LCA.declType $ snd pd
          pn = genParamName pd

isin :: LCA.Declaration d => Set LCA.IdentDecl -> d -> Bool
isin ps pdec = any (\idec -> LCA.declIdent idec == LCA.declIdent pdec) ps

isdep :: LCA.Declaration d => Set ParDep -> d -> Bool
isdep pds pdec = any (\(idec,_,_,_) -> LCA.declIdent idec == LCA.declIdent pdec) pds

namEntry :: LCA.Declaration a => String -> a -> (String, JSValue)
namEntry prefix decl = ("f_name", showJSON $ prefix ++ getDeclName decl)

comEntry = ("f_comments", showJSON "")
locEntry sfn = ("f_def_loc", showJSON $ sfn)
nmpEntry ftyp = ("f_num_params", getNumParams ftyp)
nmiEntry invokes = ("f_num_invocations", showJSON $ length invokes)
invEntry invokes = ("f_invocations", showJSON $ invokes)

-- | Translate an invocation, given as a 'CGFunInvoke', to a JSON object.
-- Additional parameters: a set of parameter dependencies, to be displayed in the invocation,
-- and the source file name (used as prefix for invocations of functions with internal linkage).
transInvocation :: Set ParDep -> String -> CGFunInvoke -> CTrav (Maybe (JSObject JSValue))
transInvocation pardeps sfnx fi@(fd,cgd,loc) = do
    sfn <- srcFileName cgd
    transInvk fpdeps ((getNamPrefix fi sfn)++namstr) (LCA.declType cgd) $ invokeAnum cgd
    where (LCI.Ident namstr _ _) = LCA.declIdent cgd
          fpdeps = S.filter (\(_,_,invk,_) -> invk == cgd) pardeps

getGlobalNamPrefix :: LCA.Declaration d => d -> String -> String
getGlobalNamPrefix idec sfn = (linkagePrefix idec sfn False) ++ (pointerPrefix idec)

getGlobalMemberPrefix :: LCI.Ident -> LCA.MemberDecl -> String
getGlobalMemberPrefix cid mdecl = (memberPrefix cid) ++ (pointerPrefix mdecl)

getNamPrefix :: CGFunInvoke -> String -> String
getNamPrefix fi@(_,idec,loc) sfn = 
    (linkagePrefix idec sfn loc) ++ (localPrefix fi) ++ (memberInvkPrefix idec) ++ (pointerPrefix idec)

linkagePrefix :: LCA.Declaration d => d -> String -> Bool -> String
linkagePrefix idec sfn False | isInternal idec = prefix ++ ":"
    where prefix = if (takeExtension sfn) == ".c" then (takeBaseName sfn) else (takeFileName sfn)
          isInternal idec = 
            case LCA.declStorage idec of
                 NoStorage -> False -- function pointer struct members
                 _ -> LCA.declLinkage idec == LCA.InternalLinkage
linkagePrefix _ _ _ = ""

localPrefix :: CGFunInvoke -> String
localPrefix (fd,_,True) = (getDeclName fd) ++ "/"
localPrefix _ = ""

memberInvkPrefix :: CGInvoke -> String
memberInvkPrefix (MemberInvoke (LCA.CompType (LCI.NamedRef cid) _ _ _ _) _ _) = memberPrefix cid
memberInvkPrefix _ = ""

memberPrefix :: LCI.Ident -> String
memberPrefix (LCI.Ident idnam _ _) = idnam ++ "."

pointerPrefix :: LCA.Declaration d => d -> String
pointerPrefix idec = 
    case resolveTypedef $ LCA.declType idec of
         LCA.PtrType _ _ _ -> "*"
         _ -> ""

getDeclName :: LCA.Declaration d => d -> String
getDeclName = LCI.identToString . LCA.declIdent

getNumParams :: LCA.FunType -> JSValue
getNumParams (LCA.FunTypeIncomplete _) = showJSON "unknown"
getNumParams (LCA.FunType _ _ True) = showJSON "variadic"
getNumParams (LCA.FunType _ pars _) = showJSON $ length pars

transInvk :: Set ParDep -> String -> LCA.Type -> Int -> CTrav (Maybe (JSObject JSValue))
transInvk _ _ (LCA.FunctionType (LCA.FunType _ [] False) _) _ = return Nothing
transInvk pardeps namstr (LCA.FunctionType ftyp _) anm = do
    parlist <- case ftyp of
                    (LCA.FunTypeIncomplete _) -> return $ map (transInvkUPar pardeps) $ take anm $ iterate (1+) 1
                    (LCA.FunType _ pars _) -> mapM (transInvkParam pardeps) $ numberList pars
    return $ Just $ toJSObject $ [nam,nmp] ++ parlist
    where nam = ("name", showJSON namstr)
          nmp = ("num_params", getNumParams ftyp)
transInvk pardeps namstr (LCA.PtrType typ _ _) anm = transInvk pardeps namstr typ anm
transInvk pardeps namstr (LCA.TypeDefType (LCA.TypeDefRef _ typ _) _ _) anm = transInvk pardeps namstr typ anm
transInvk _ _ _ _ = return Nothing

transInvkUPar :: Set ParDep -> Int -> (String,JSValue)
transInvkUPar pdeps idx = (show idx,depsAsJSON $ S.filter (\(_,_,_,i) -> i == idx) pdeps)

transInvkParam :: Set ParDep -> (Int,LCA.ParamDecl) -> CTrav (String,JSValue)
transInvkParam pdeps pd = do
    val <- genDependency pdeps pd
    return (genParamName pd,val)

genDependency :: Set ParDep -> (Int,LCA.ParamDecl) -> CTrav JSValue
genDependency pdeps (idx,pdecl) = do
    lin <- isLinearParType dtyp 
    if lin
       then do
           ro <- isReadOnlyParType dtyp
           return $ if ro 
                       then showJSON "readonly" 
                       else depsAsJSON $ S.filter (\(_,_,_,i) -> i == idx) pdeps
       else return $ showJSON "nonlinear"
    where dtyp = LCA.declType $ pdecl

depsAsJSON :: Set ParDep -> JSValue
depsAsJSON pdeps = showJSON $ map (\(pd,pi,_,_) -> showJSON $ (show pi) ++ "-" ++ (LCI.identToString $ LCA.declIdent pd)) $ toList pdeps

-- | A parameter name of the form N-xxx or N where N is the parameter number (starting with 1) and 
-- xxx is the declared parameter name, if available.
genParamName :: (Int,LCA.ParamDecl) -> String
genParamName (idx,pdecl) = (show idx) ++ nam
    where (LCA.VarDecl vnam _ _) = LCA.getVarDecl pdecl
          nam = case vnam of
                     (LCA.VarName (LCI.Ident namstr _ _) _) -> "-" ++ namstr
                     (LCA.NoName) -> ""

numberList :: [a] -> [(Int,a)]
numberList l = zip (iterate (1 +) 1) l 

maybeNumberList :: [Maybe a] -> [Maybe (Int,a)]
maybeNumberList l = zipWith maybePair (iterate (1 +) 1) l 

maybePair :: b -> Maybe a -> Maybe (b,a)
maybePair _ Nothing = Nothing
maybePair x (Just y) = Just (x,y)
