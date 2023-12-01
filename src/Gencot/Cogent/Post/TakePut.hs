{-# LANGUAGE PackageImports #-}
module Gencot.Cogent.Post.TakePut where

import Data.List (break)

import Language.C.Data.Error
import Language.C.Analysis as LCA (Trav,recordError,getUserState,modifyUserState)

import Cogent.Surface as CS
import Cogent.Common.Syntax as CCS

import Gencot.Names (ptrDerivCompName)
import Gencot.Cogent.Ast
import Gencot.Cogent.Error (takeOp)
import Gencot.Cogent.Types (
  isUnsizedArrayType, isArrayType, isNonlinear, isRegular, isMayNull, isPtrType, isVoidPtrType, isReadonly, isUnitType,
  mkU32Type, mkTupleType, mkUnboxed, mkFunType, getMemberType, getDerefType, getResultType,
  isUnboxedMember, isUnboxedDeref, tupleSize)
import Gencot.Cogent.Bindings (errVar, toDummyExpr, mkDummyExpr, isTakeBinding, isPutBindingFor, isTakePattern, isArrayTakePattern,
  mkUnitPattern, mkVarPattern, mkTuplePattern, mkVarTuplePattern, mkTupleBinding)
import Gencot.Cogent.Expr (TypedVar(TV), typOfTV, mkUnitExpr, mkIntLitExpr, mkVarExpr, mkTupleExpr, mkVarTupleExpr,
  mkAppExpr, mkTopLevelFunExpr, mkMemberExpr, mkLambdaExpr, mkLetExpr)
import Gencot.Cogent.Post.Util (ETrav, freeInExpr, freeInPatn, freeInIrrefPatn,
  modifiedByBindings, varUsedIn, freeTypedVarsUnderBinding, boundTypedVarsInBindings)

{- Process take- and put-bindings -}
{- Detect and record errors.      -}
{----------------------------------}


tpproc :: GenExpr -> ETrav GenExpr
tpproc e = do
    e1 <- tpsingle e
    return $ tpmodify $ tpelim e1

-- | Process individual take- and put-bindings according to the container type.
-- If the container has MayNull type: error
-- If the container has abstract type: error
-- If the container has readonly type: convert take to member or getArr access.
-- If the container is the error variable: convert take to dummy binding for component variable.
-- If the component is cont for a record or array: error.
-- In all cases the put-binding is simply removed.
tpsingle :: GenExpr -> ETrav GenExpr
tpsingle (GenExpr (CS.Let bs bdy) o t c) = do
    bs' <- tpsingleBindings bs
    bdy' <- tpsingle bdy
    return $ if null bs' then bdy' else GenExpr (CS.Let bs' bdy') o t c
tpsingle e =
    mapMExprOfGE (mapM tpsingle) e

tpsingleBindings :: [GenBnd] -> ETrav [GenBnd]
tpsingleBindings [] = return []
tpsingleBindings (b@(CS.Binding ip m e bvs) : bs)
    | (GenIrrefPatn (CS.PTake _ _) _ _) <- ip = do
        b' <- tpsingleTake b
        bs' <- tpsingleBindings bs
        return (b' : bs')
tpsingleBindings (b@(CS.Binding ip m e bvs) : bs)
    | (GenIrrefPatn (CS.PArrayTake _ _) _ _) <- ip = do
        b' <- tpsingleArrayTake b
        bs' <- tpsingleBindings bs
        return (b' : bs')
tpsingleBindings ((CS.Binding _ _ (GenExpr (CS.Put pv [Just (f,_)]) _ t _) _) : bs)
    | isMayNull t
      || isVoidPtrType t
      || isReadonly t
      || f == ptrDerivCompName && ((isUnitType mtype) || (mtype == mkUnboxed t))
    = tpsingleBindings bs
    where mtype = getMemberType f t
tpsingleBindings ((CS.Binding _ _ (GenExpr (CS.ArrayPut pv _) _ t _) _) : bs)
    | isMayNull t
      || isVoidPtrType t
      || isReadonly t
    = tpsingleBindings bs
tpsingleBindings ((CS.Binding ip m e bvs) : bs) = do
    e' <- tpsingle e
    bs' <- tpsingleBindings bs
    return ((CS.Binding ip m e' bvs) : bs')

tpsingleTake :: GenBnd -> ETrav GenBnd
tpsingleTake b@(CS.Binding ip m e bvs)
    | (GenIrrefPatn (CS.PTake pv [Just (f,cip)]) o t) <- ip =
    let (err,msg) =
            if f == ptrDerivCompName && (isArrayType t)
               then (False, "arrderef")
               else if isMayNull t
               then (True, "Dereferencing pointer which may be NULL")
               else if isVoidPtrType t
               then (True, "Dereferencing void pointer")
               else if isReadonly t || (isRegular t && pv == errVar)
               then (False, "nonlinear")
               else if pv == errVar
               then (True, "Dereferencing pointer not specified by a variable")
               else if f == ptrDerivCompName && ((isUnitType mtype) || (mtype == mkUnboxed t))
               then (True, "Dereferencing pointer to a record")
               else (False,"")
        mtype = getMemberType f t
        dummy = toDummyExpr e $ mkDummyExpr (typOfGIP cip) msg
        ipa = (GenIrrefPatn (CS.PArrayTake pv [(idx0,cip)]) o t)
        idx0 = mkIntLitExpr mkU32Type 0
    in if err
       then do
           recordError $ takeOp (orgOfGE e) msg
           return $ CS.Binding cip Nothing dummy []
       else if null msg
       then return b
       else if msg == "nonlinear"
       then return $ toNonLinAccess b
       else -- arrderef
         tpsingleArrayTake $ CS.Binding ipa m e bvs
tpsingleArrayTake :: GenBnd -> ETrav GenBnd
tpsingleArrayTake b@(CS.Binding ip _ e _)
    | (GenIrrefPatn (CS.PArrayTake pv [(_,cip)]) _ t) <- ip =
    let (err,msg) =
            if not $ isArrayType t
               then (True, "Accessing array element of non-array pointer.")
               else if isMayNull t
               then (True, "Accessing element of array which may be NULL")
               else if isVoidPtrType t
               then (True, "Accessing element of void pointer")
               else if isUnsizedArrayType t
               then (True, "Accessing element of array without known size.")
               else if isReadonly t
               then (False, "readonly")
               else if pv == errVar
               then (True, "Accessing element of array not specified by a variable")
               else (False,"")
        dummy = toDummyExpr e $ mkDummyExpr (typOfGIP cip) msg
    in if err
       then do
           recordError $ takeOp (orgOfGE e) msg
           return $ CS.Binding cip Nothing dummy []
       else if null msg
       then return b
       else -- readonly
         return $ toNonLinAccess b

-- | Convert a take binding to a member access or application of getPtr or gerArr.
toNonLinAccess :: GenBnd -> GenBnd
toNonLinAccess (CS.Binding ip m e bvs)
    | (GenIrrefPatn (CS.PTake pv [Just (f,cip)]) o t) <- ip =
    let mtype = getMemberType f t
        mexpr = if isPtrType t
                   then mkAppExpr (mkTopLevelFunExpr ("getPtr", mkFunType t mtype) [Just t, Just mtype]) $ e
                   else if isReadonly t && isUnboxedMember f t
                   then mkAppExpr (mkTopLevelFunExpr ("getrefFld_" ++ f, mkFunType t mtype) [Just t, Just mtype]) $ e
                   else mkMemberExpr mtype e f
    in CS.Binding cip Nothing mexpr []
toNonLinAccess (CS.Binding ip m e bvs)
    | (GenIrrefPatn (CS.PArrayTake pv [(idx,cip)]) _ t) <- ip =
    let etype = getDerefType t
        eexpr = if isReadonly t && isUnboxedDeref t
                   then mkAppExpr (mkTopLevelFunExpr ("getrefArr", mkFunType t etype) [Just t, Just mkU32Type, Just etype]) $ mkTupleExpr [e,idx]
                   else mkAppExpr (mkTopLevelFunExpr ("getArr", mkFunType t etype) [Just t, Just mkU32Type, Just etype]) $ mkTupleExpr [e,idx]
    in CS.Binding cip Nothing eexpr []

-- | Eliminate take or put bindings.
-- A take binding can be eliminated if the old component value is not used.
-- A put binding can be eliminated if the component is not modified
-- and the take binding can be eliminated or converted to a member access,
-- so that it does not produce a taken type for the container.
tpelim :: GenExpr -> GenExpr
tpelim (GenExpr (CS.Let bs bdy) o t c) =
    if null bs' then bdy' else GenExpr (CS.Let bs' bdy') o t c
    where bs' = tpelimInBindings bs bdy
          bdy' = tpelim bdy
tpelim e =
    mapExprOfGE (fmap tpelim) e

tpelimInBindings :: [GenBnd] -> GenExpr -> [GenBnd]
tpelimInBindings [] bdy = []
tpelimInBindings (tkb@(CS.Binding ip _ _ _) : bs) bdy | isTakePattern ip =
    scp' ++ bs'
    where (cmp,scp,ptb,rst) = getTakePutScope tkb bs
          scp' = tpelimForTake cmp tkb scp ptb rst bdy
          bs' = tpelimInBindings rst bdy
tpelimInBindings ((CS.Binding ip m e bvs) : bs) bdy =
    (CS.Binding ip m (tpelim e) bvs) : (tpelimInBindings bs bdy)

-- | Process a pair of take and put bindings or arrayTake and arrayPut binding.
-- The result is the sequence of processed bindings from take to put.
-- Nested take/put bindings are also processed.
-- The first argument is the taken component variable.
-- The following three arguments are the take binding, the bindings between take and put and the put binding.
-- The fifth argument is the list of bindings following the put binding.
-- The last argument is the let body following all bindings.
tpelimForTake :: TypedVar -> GenBnd -> [GenBnd] -> GenBnd -> [GenBnd] -> GenExpr -> [GenBnd]
tpelimForTake (TV cmp ct) tkb@(CS.Binding ip _ (GenExpr _ _ t _) _) scp ptb rst bdy =
    if needPut
       then if needTake (scp' ++ (ptb : rst))
         then (if isRegular t then toNonLinAccess tkb else tkb) : (scp' ++ [ptb])
         else  scp' ++ [setIfArray ptb]
         else if needTake (scp' ++ rst)
         then (toNonLinAccess tkb) : scp'
         else scp'
    where (pre,nst) = break isTakeBinding scp -- nested take binding is first in nst
          scp' = if null nst
                    then pre
                    else let ntkb = head nst
                             (ncmp,nscp,nptb,nrst) = getTakePutScope ntkb (tail nst)
                             nscp' = tpelimForTake ncmp ntkb nscp nptb (nrst ++ rst) bdy
                         in pre ++ nscp' ++ nrst
          needTake bs = (varUsedIn cmp bs bdy) || (not $ isNonlinear ct)
          needPut = (elem cmp $ modifiedByBindings scp') || (not $ isNonlinear t)

-- | Retrieve the scope of a take binding from a binding sequence.
-- The first argument is a take binding.
-- The result is the component variable, the binding sequence before the put, the put binding, and the binding sequence after the put.
getTakePutScope :: GenBnd -> [GenBnd] -> (TypedVar, [GenBnd], GenBnd, [GenBnd])
getTakePutScope tkb bs =
    (tv, scp, head rst, tail rst)
    where tv@(TV cmp ct) = getCmpVarFromTake tkb
          (scp,rst) = break (isPutBindingFor cmp) bs -- put binding is first in rst, must be present

getCmpVarFromTake :: GenBnd -> TypedVar
getCmpVarFromTake (CS.Binding (GenIrrefPatn (CS.PTake _ [Just (_,(GenIrrefPatn (CS.PVar cv) _ ct))]) _ _) _ _ _) = TV cv ct
getCmpVarFromTake (CS.Binding (GenIrrefPatn (CS.PArrayTake _ [(_,(GenIrrefPatn (CS.PVar cv) _ ct))]) _ _) _ _ _) = TV cv ct

-- | Convert array put to setArr application.
setIfArray :: GenBnd -> GenBnd
setIfArray (CS.Binding ip Nothing (GenExpr (CS.ArrayPut e [(idx,ee)]) _ t _) []) =
    mkTupleBinding [ip,mkUnitPattern] $
      mkAppExpr (mkTopLevelFunExpr ("setArr", setArrType) [Just t, Just mkU32Type, Just etype]) $ mkTupleExpr [e,idx,ee]
    where setArrType = mkFunType (mkTupleType [t,mkU32Type,etype]) (mkTupleType [t,unitType])
          etype = typOfGE ee
setIfArray b = b

-- | Convert pairs of take and put bindings to modify applications.
tpmodify :: GenExpr -> GenExpr
tpmodify (GenExpr (CS.Let bs bdy) o t c) =
    if null bs' then bdy' else GenExpr (CS.Let bs' bdy') o t c
    where bs' = tpmodifyInBindings bs bdy
          bdy' = tpmodify bdy
tpmodify e =
    mapExprOfGE (fmap tpmodify) e

tpmodifyInBindings :: [GenBnd] -> GenExpr -> [GenBnd]
tpmodifyInBindings [] bdy = []
tpmodifyInBindings (tkb@(CS.Binding ip _ _ _) : bs) bdy | isTakePattern ip =
    scp' ++ bs'
    where (cmp,scp,ptb,rst) = getTakePutScope tkb bs
          scp' = tpmodifyForTake cmp tkb scp ptb rst bdy
          bs' = tpmodifyInBindings rst bdy
tpmodifyInBindings ((CS.Binding ip m e bvs) : bs) bdy =
    (CS.Binding ip m (tpmodify e) bvs) : (tpmodifyInBindings bs bdy)

-- | Process a pair of take and put bindings or arrayTake and arrayPut binding.
-- The result is the single binding for a modify application
-- or the binding sequence from take to put with processed nested take/put pairs.
-- The first argument is the taken component variable.
-- The following three arguments are the take binding, the bindings between take and put and the put binding.
-- The fifth argument is the list of bindings following the put binding.
-- The last argument is the let body following all bindings.
tpmodifyForTake :: TypedVar -> GenBnd -> [GenBnd] -> GenBnd -> [GenBnd] -> GenExpr -> [GenBnd]
tpmodifyForTake cmp@(TV cn ct) tkb@(CS.Binding ip _ _ _) scp ptb rst bdy =
    if doModif
       then [if iscf
             then mkModBinding ip cf cps ces
             else mkModBinding ip chfun (mkVarsOrUnitPatterns outvars) (mkVarsOrUnitExprs inpvars)]
       else tkb : (scp' ++ [ptb])
    where doModif = isArrayTakePattern ip || cmpIsUnboxedInLin ip
          (pre,nst) = break isTakeBinding scp -- nested take binding is first in nst
          scp' = if null nst
                    then pre
                    else let ntkb = head nst
                             ntkb' = elimPreBind pre ntkb
                             (ncmp,nscp,nptb,nrst) = getTakePutScope ntkb' (tail nst)
                             nscp' = tpmodifyForTake ncmp ntkb' nscp nptb (nrst ++ rst) bdy
                         in nscp' ++ nrst
          (iscf,cf,cps,ces) = checkChgFunFor cmp scp'
          outvars = filter (\(TV v _) -> varUsedIn v rst bdy) $ (cmp : boundTypedVarsInBindings scp')
          chbdy = mkTupleExpr ((mkVarExpr cmp) : mkVarsOrUnitExprs outvars)
          inpvars = filter (\(TV v _) -> varUsedIn v scp' chbdy) $ freeTypedVarsUnderBinding (tkb : scp') (cmp: outvars)
          chargs = mkTuplePattern ((mkVarPattern cmp) : mkVarsOrUnitPatterns inpvars)
          chfun = mkLambdaExpr chargs (if null scp' then chbdy else mkLetExpr scp' chbdy)

cmpIsUnboxedInLin :: GenIrrefPatn -> Bool
cmpIsUnboxedInLin (GenIrrefPatn (CS.PTake _ [Just (f,_)]) _ t) = isUnboxedMember f t && (not $ isNonlinear t)
cmpIsUnboxedInLin (GenIrrefPatn (CS.PArrayTake _ _) _ t) = isUnboxedDeref t && (not $ isNonlinear t)

-- | Substitute value variable binding for the container of a nested take.
elimPreBind :: [GenBnd] -> GenBnd -> GenBnd
elimPreBind [CS.Binding (GenIrrefPatn (CS.PVar pv) _ _) _ (GenExpr (CS.Var v) _ _ _) _]
                (CS.Binding ip m (GenExpr (CS.Var v2) o t c) bvs) | v2 == pv =
    CS.Binding ip m (GenExpr (CS.Var v) o t c) bvs
elimPreBind _ _ = error "Unexpected binding(s) between nested takes."

-- | Check whether a binding sequence is a single change function application for a variable of the form
--   (pv,outvars..) = chfun (pv,inpvars..)
-- The first component of the result is True if the binding sequence is a single binding
-- of this form and the remaining results are chfun, outvars.., and inpvars..
-- Otherwise the remaining results are the unit expression and two empty lists.
checkChgFunFor :: TypedVar -> [GenBnd] -> (Bool, GenExpr, [GenIrrefPatn], [GenExpr])
checkChgFunFor (TV v _) [CS.Binding (GenIrrefPatn (CS.PTuple ((GenIrrefPatn (CS.PVar pv) _ _) : ips)) _ _) _
                          (GenExpr (CS.App f (GenExpr (CS.Tuple ((GenExpr (CS.Var ev) _ _ _) : es)) _ _ _) _) _ _ _) []]
    | pv == v && ev == v = (True,f,ips,es)
checkChgFunFor _ _ = (False,mkUnitExpr,[],[])

-- | Construct a binding with a modify application.
-- It has the form (v,outvars..) = modify (v, [idx,] chfun, inpvars..)
-- The first argument is the original take pattern, used to determine v, idx, and modify.
-- The second argument is the change function chfun.
-- The third argument is the list of patterns outvars..
-- The last argument is the list of expressions inpvars..
mkModBinding :: GenIrrefPatn -> GenExpr -> [GenIrrefPatn] -> [GenExpr] -> GenBnd
mkModBinding ip@(GenIrrefPatn (CS.PTake pv _) _ t) f ips es =
    mkModBinding' (TV pv t) ip ips [f] es
mkModBinding ip@(GenIrrefPatn (CS.PArrayTake pv [(idx,_)]) _ t) f ips es =
    mkModBinding' (TV pv t) ip ips [idx, f] es

mkModBinding' tv ip ips idxandfun es =
    CS.Binding (mkTuplePattern ((mkVarPattern tv) : ips)) Nothing (mkAppExpr modfun modargs) []
    where modargs = mkTupleExpr ((mkVarExpr tv) : (idxandfun ++ es))
          chfun = last idxandfun
          modfuntype = mkFunType (typOfGE modargs) $ getResultType $ typOfGE chfun
          modfun = mkModFun ip modfuntype

-- | Construct an expression for the modify function from the take pattern.
-- The second argument is the type to be used for the resulting modify function.
mkModFun :: GenIrrefPatn -> GenType -> GenExpr
mkModFun ip@(GenIrrefPatn (CS.PTake pv [Just (f,(GenIrrefPatn (CS.PVar cv) _ ct))]) _ t) modfuntype =
    mkTopLevelFunExpr (modfunname, modfuntype) [Just t, Just ct, Nothing, Nothing]
    where modfunname = if cmpIsUnboxedInLin ip && (not $ isNonlinear ct)
                          then "modrefFld_" ++ f
                          else if isPtrType t
                          then "modifyPtr"
                          else "modifyFld_" ++ f
mkModFun ip@(GenIrrefPatn (CS.PArrayTake pv [(_,(GenIrrefPatn (CS.PVar cv) _ ct))]) _ t) modfuntype =
    mkTopLevelFunExpr (modfunname, modfuntype) [Just t, Just mkU32Type, Just ct, Nothing, Nothing]
    where modfunname = if cmpIsUnboxedInLin ip && (not $ isNonlinear ct)
                          then "modrefArr"
                          else "modifyArr"

mkVarsOrUnitPatterns :: [TypedVar] -> [GenIrrefPatn]
mkVarsOrUnitPatterns [] = [mkUnitPattern]
mkVarsOrUnitPatterns vars = map mkVarPattern vars

mkVarsOrUnitExprs :: [TypedVar] -> [GenExpr]
mkVarsOrUnitExprs [] = [mkUnitExpr]
mkVarsOrUnitExprs vars = map mkVarExpr vars
