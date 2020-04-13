{-# LANGUAGE PackageImports, TypeSynonymInstances, FlexibleInstances #-}

-- | Translate C Code to JSON function descriptions.
module Gencot.Json.Translate where

import Data.Set (Set,size,toList,empty,union,fromList,insert,unions,singleton)
import qualified Data.Set as S (filter)
import Data.Maybe (fromJust,catMaybes,mapMaybe)
import Data.List (elemIndex,isSuffixOf)
import Control.Monad (liftM)
import Data.Foldable (foldlM)
import Text.JSON

import "language-c" Language.C as LC hiding (pretty,Pretty)
import Language.C.Data.Ident as LCI
import Language.C.Data.Node as LCN
import Language.C.Data.Position as LCP
import Language.C.Analysis as LCA hiding (mapMaybeM)

import Gencot.Traversal (stopResolvTypeName)
import Gencot.Util.CallGraph (CallGraph,CGFunInvoke,CGInvoke(IdentInvoke,MemberInvoke),CTrav,lookupCallGraph,invokeAnum,unionM,foldsets,getCGInvoke,invokeType,invokeParams)
import Gencot.Util.Types (isLinearParType,isReadOnlyParType,isFunction,resolveTypedef,isSIFType,getFunctionInSIFType,mergeQualsTo,getFunType,isPointer,isArray,isExtern)
import Gencot.Util.Expr (getRootIdent,isReference)
import Gencot.Util.Decl (traverseLocalDecl)
import Gencot.Names (srcFileName)
import Gencot.Json.Parmod (Parmod,Parmods)
import Gencot.Json.Process (mergeParmods)
import Gencot.Items.Types (getIndividualItemId,getTagItemId,getTypedefItemId,getMemberSubItemId,getParamSubItemId,getFunctionSubItemId)
import Gencot.Items.Identifier (paramSubItemId) -- only temporary

qmark = showJSON "?"
jsEmpty = JSArray []

-- | Translate a sequence of C global declarations to a sequence of function descriptions.
transGlobals :: [LCA.DeclEvent] -> CTrav Parmods
transGlobals evs = (liftM concat) $ (mapM transGlobal) evs 

-- | Translate a C global declaration to a sequence of function descriptions.
-- Every function definition and declaration is translated to a function description.
-- Additional descriptions are generated for items with a declared SIF (syntactically including function) type.
-- For each invocation which invokes a local item (a parameter or local variable) of a SIF type, 
--   a function description for the local function item is appended.
-- Every object definition or declaration of SIF type is translated to a function description.
-- For every definition of a compound type all members of SIF type are translated to function descriptions.
-- Definitions of type names for SIF types are translated to function descriptions.
-- All other global declarations are ignored.
transGlobal :: LCA.DeclEvent -> CTrav Parmods
transGlobal (LCA.DeclEvent idec@(LCA.FunctionDef fdef)) = do
    sfn <- srcFileName fdef
    cg <- (liftM toList) $ lookupCallGraph $ LCA.declIdent fdef
    parmods <- findParModifs fdef
    pardeps <- findParDepnds fdef
    let fpardeps = S.filter (\(decl,_,_,_) -> not $ isin parmods decl) pardeps
    parlist <- mapM (paramEntry parmods fpardeps) $ numberList pars
    tinvokes <- mapM (transInvocation fpardeps sfn) cg
    let invokes = catMaybes tinvokes
    funpars <- mapMaybeM (transParam (getIndividualItemId idec sfn) sfn) (numberList pars)
    let localcg = filter (\(_,_,loc) -> loc) cg
    locals <- mapM (transLocal sfn) localcg
    return $ [toJSObject ([namEntry (getIndividualItemId idec sfn),comEntry,locEntry sfn,nmpEntry ftyp] ++ parlist ++ 
                [nmiEntry invokes] ++ if not (null invokes) && (any maymodify parlist) then [invEntry invokes] else [])] 
        ++ (mergeParmods funpars locals)
    where (LCA.FunctionType ftyp@(LCA.FunType restype pars isVar) _) = LCA.declType fdef
          maymodify (_,jss) = jss == qmark || jss == showJSON "?depends"
transGlobal (LCA.DeclEvent idec@(LCA.ObjectDef odef)) | isSIFType $ LCA.declType idec =
    transDecl idec $ getFunType $ getFunctionInSIFType $ LCA.declType idec
transGlobal (LCA.DeclEvent idec@(LCA.Declaration decl)) = do
    rtyp <- if isExtern idec then resolveExternalType typ else return typ
    if isSIFType rtyp 
       then transDecl idec $ getFunType $ getFunctionInSIFType rtyp
       else return $ []
    where typ = LCA.declType idec
transGlobal (LCA.TagEvent cd@(LCA.CompDef (LCA.CompType sueref knd mdecls _ _))) =
    mapMaybeM (transMember sueref knd $ isExtern cd) mdecls
transGlobal (LCA.TypeDefEvent tdef@(LCA.TypeDef nam typ _ _)) = do
    rtyp <- if isExtern tdef then resolveExternalType typ else return typ
    if isSIFType rtyp 
       then do
           sfn <- srcFileName tdef
           let ftyp@(LCA.FunType restype pars isVar) = getFunType $ getFunctionInSIFType rtyp
           parlist <- mapM simpleParamEntry $ numberList pars
           return $ [toJSObject ([tdNamEntry tdef,comEntry,locEntry sfn,nmpEntry ftyp] ++ parlist)]
       else return $ []
transGlobal _ = return $ []

mapMaybeM :: Monad m => (a -> m (Maybe b)) -> [a] -> m [b]
mapMaybeM f = liftM catMaybes . mapM f

-- | Translate a declaration with SIF type to a sequence (of length 1) of function descriptions.
transDecl :: LCA.IdentDecl -> LCA.FunType -> CTrav Parmods
transDecl decl ftyp@(LCA.FunType _ pars isVar) = do
    sfn <- srcFileName decl
    parlist <- mapM simpleParamEntry $ numberList pars
    funpars <- if isFunction typ then mapMaybeM (transParam (getIndividualItemId decl sfn) sfn) (numberList pars) else return []
    return $ [toJSObject ([namEntry (getFunctionSubItemId typ $ getIndividualItemId decl sfn),comEntry,locEntry sfn,nmpEntry ftyp] ++ parlist)] 
                ++ funpars
    where typ = LCA.declType decl
transDecl decl ftyp@(LCA.FunTypeIncomplete _) = do
    sfn <- srcFileName decl
    return $ [toJSObject ([namEntry (getFunctionSubItemId typ $ getIndividualItemId decl sfn),comEntry,locEntry sfn,nmpEntry ftyp])] 
    where typ = LCA.declType decl

-- | Translate a struct or union member to a function description, if it has a SIF type.
transMember :: LCI.SUERef -> LCA.CompTyKind -> Bool -> LCA.MemberDecl -> CTrav (Maybe Parmod)
transMember sueref knd extrn mdecl = do
    rtyp <- if extrn then resolveExternalType typ else return typ
    if isSIFType rtyp 
       then do
           sfn <- srcFileName mdecl
           liftM (Just . head) $ transMemberDecl sfn (getMemberSubItemId (getTagItemId sueref knd) mdecl) rtyp
              $ getFunType $ getFunctionInSIFType rtyp
       else return Nothing
    where typ = LCA.declType mdecl

-- | Translate a member declaration with a SIF type to a sequence (of length 1) of function descriptions.
-- itemId is the item id of the member.
transMemberDecl :: String -> String -> LCA.Type -> LCA.FunType -> CTrav Parmods
transMemberDecl sfn itemId rtyp ftyp@(LCA.FunType _ pars isVar) = do
    parlist <- mapM simpleParamEntry $ numberList pars
    funpars <- if isFunction rtyp then mapMaybeM (transParam itemId sfn) (numberList pars) else return []
    return $ [toJSObject ([namEntry $ getFunctionSubItemId rtyp itemId,comEntry,locEntry sfn,nmpEntry ftyp] ++ parlist)] 
                ++ funpars
transMemberDecl sfn itemId rtyp ftyp@(LCA.FunTypeIncomplete _) = do
    return $ [toJSObject ([namEntry $ getFunctionSubItemId rtyp itemId,comEntry,locEntry sfn,nmpEntry ftyp])] 

-- | Translate a function parameter, if it has a SIF type.
-- Other function parameters are only described (by transLocal), if they are invoked.
-- The first argument is the item id of the function containing the parameter.
transParam :: String -> String -> (Int,LCA.ParamDecl) -> CTrav (Maybe Parmod)
transParam iid sfn (pos,pd) | isSIFType ptyp = do
    parlist <- mapM simpleParamEntry $ numberList pars
    return $ Just $ toJSObject $ [namEntry $ getFunctionSubItemId ptyp (getParamSubItemId iid (pos,pd)),comEntry,locEntry sfn,nmpEntry ftyp] ++ parlist
    where ptyp = LCA.declType pd
          ftyp@(LCA.FunType restype pars isVar) = getFunType $ getFunctionInSIFType ptyp
transParam _ _ _ = return Nothing

-- | Translate an invocation of a local item of SIF type to a function description.
transLocal :: String -> CGFunInvoke -> CTrav Parmod
transLocal sfn fi@(fd,invk@(IdentInvoke idec _),_) = do
    parlist <- mapM simpleParamEntry $ numberList $ invokeParams invk
    return $ toJSObject $ [namEntry $ getFunctionSubItemId ptyp parItemId,comEntry,locEntry sfn,nmpEntry $ invokeType invk] ++ parlist
    where ptyp = LCA.declType idec
          parItemId = -- (getParamSubItemId (getIndividualItemId (LCA.FunctionDef fd) sfn) (pos,pdec))  -- use this when pos and pdec are available
            paramSubItemId (getIndividualItemId (LCA.FunctionDef fd) sfn) 0 $ LCI.identToString $ LCA.declIdent idec

-- | Resolve an external type.
-- Must be a monadic action because it needs the type names where to stop resolving.
resolveExternalType :: LCA.Type -> CTrav LCA.Type
resolveExternalType td@(LCA.TypeDefType (LCA.TypeDefRef nam t _) quals _) = do
    stop <- stopResolvTypeName nam
    if stop then return td else resolveExternalType (mergeQualsTo t quals)
resolveExternalType (LCA.PtrType t q a) = do
    t' <- resolveExternalType t
    return $ LCA.PtrType t' q a
resolveExternalType (LCA.ArrayType t i q a) = do
    t' <- resolveExternalType t
    return $ LCA.ArrayType t' i q a
resolveExternalType (LCA.FunctionType (LCA.FunType rt pars v) a) = do
    rt' <- resolveExternalType rt
    pars' <- mapM resolveExternalTypesInParDecl pars
    return $ LCA.FunctionType (LCA.FunType rt' pars' v) a
resolveExternalType (LCA.FunctionType (LCA.FunTypeIncomplete rt) a) = do
    rt' <- resolveExternalType rt
    return $ LCA.FunctionType (LCA.FunTypeIncomplete rt') a
resolveExternalType t = return t

resolveExternalTypesInParDecl (LCA.ParamDecl (LCA.VarDecl vn a t) n) = do
    t' <- resolveExternalType t
    return $ LCA.ParamDecl (LCA.VarDecl vn a t') n
resolveExternalTypesInParDecl (LCA.AbstractParamDecl (LCA.VarDecl vn a t) n) = do
    t' <- resolveExternalType t
    return $ LCA.AbstractParamDecl (LCA.VarDecl vn a t') n

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
    findParMods p (LC.CAssign _ (LC.CIndex (LC.CVar sid _) iexpr _) expr _) = do
        {- special case if sid is of array type, only modified if adjusted parameter -}
        res <- unionM (findParMods p iexpr) (findParMods p expr)
        mldec <- LCA.lookupObject sid
        case mldec of
             Nothing -> return res
             Just ldec -> if any (\(_,idec) -> LCA.declIdent idec == LCA.declIdent ldec) p
                          then return $ insert ldec res 
                          else return res
    findParMods p (LC.CAssign _ lexpr expr _) = 
        unionM (lvalParMod p lexpr) $ unionM (findParMods p lexpr) (findParMods p expr)
    findParMods p (LC.CCall expr args _) = unionM (findParMods p expr) (findParMods p args)
    findParMods p (LC.CComma exprs _) = findParMods p exprs
    findParMods p (LC.CCond expr1 mexpr2 expr3 _) = 
        unionM (findParMods p expr1) $ unionM (mfindParMods p mexpr2) (findParMods p expr3)
    findParMods p (LC.CBinary _ expr1 expr2 _) = unionM (findParMods p expr1) (findParMods p expr2)
    findParMods p (LC.CCast _ expr _) = findParMods p expr
    findParMods p (LC.CUnary op expr _) | isModifOp op = 
        unionM (lvalParMod p expr) (findParMods p expr)
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

instance HasParMods (Maybe LC.CDecl, LC.CExpr) where
    findParMods p (_,expr) = findParMods p expr

    findParDeps p (_,expr) = findParDeps p expr

isModifOp :: LC.CUnaryOp -> Bool
isModifOp LC.CPreIncOp = True
isModifOp LC.CPreDecOp = True
isModifOp LC.CPostIncOp = True
isModifOp LC.CPostDecOp = True
isModifOp _ = False

-- | If an lvalue is a modified parameter, return it as singleton modification
-- Only tests for some simple cases.
lvalParMod :: MonadTrav m => Set (Int,LCA.IdentDecl) -> LC.CExpr -> m (Set LCA.IdentDecl)
lvalParMod p lexpr = 
    case getRootIdent lexpr of
         Nothing -> return empty
         Just lroot -> do
             mldec <- LCA.lookupObject lroot
             case mldec of
                  Nothing -> return empty
                  Just ldec -> if any (\(_,idec) -> LCA.declIdent idec == LCA.declIdent ldec) p
                                  && isReference lexpr
                                  then return $ singleton ldec
                                  else return empty

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
                             if (null apars) || (length apars) < i -- incomplete or variadic after defined parameters
                                then return $ singleton (adec,pnum,invk,i) 
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

namEntry :: String -> (String, JSValue)
namEntry iid = ("f_name", showJSON iid)

tdNamEntry :: LCA.TypeDef -> (String, JSValue)
tdNamEntry (LCA.TypeDef nam typ _ _) = ("f_name", showJSON $ getFunctionSubItemId typ $ getTypedefItemId $ nam)

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
    iid <- getInvokeItemId sfn fi
    transInvk fpdeps iid (LCA.declType cgd) $ invokeAnum cgd
    where fpdeps = S.filter (\(_,_,invk,_) -> invk == cgd) pardeps

getInvokeItemId :: String -> CGFunInvoke -> CTrav String
getInvokeItemId sfn (_,(IdentInvoke idec _),False) = do
    rtyp <- if isExtern idec then resolveExternalType typ else return typ
    return $ getFunctionSubItemId rtyp $ getIndividualItemId idec sfn
    where typ = LCA.declType idec
getInvokeItemId sfn (_,(MemberInvoke ct@(LCA.CompType sueref knd _ _ _) mdec _),_) = do
    rtyp <- if isExtern ct then resolveExternalType typ else return typ
    return $ getFunctionSubItemId rtyp $ getMemberSubItemId (getTagItemId sueref knd) mdec
    where typ = LCA.declType mdec
getInvokeItemId sfn (fd,(IdentInvoke idec _),True) = 
    -- getParamSubItemId (getIndividualItemId fd sfn) (pos,pdec) -- use when pos and pdec are available
    return $ getFunctionSubItemId (LCA.declType idec) $ paramSubItemId (getIndividualItemId (LCA.FunctionDef fd) sfn) 0 $ LCI.identToString $ LCA.declIdent idec

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
transInvk pardeps namstr (LCA.ArrayType typ _ _ _) anm = transInvk pardeps namstr typ anm
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

