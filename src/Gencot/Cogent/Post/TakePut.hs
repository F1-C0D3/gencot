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
  isUnsizedArrayType, isArrayType, isNonlinear, isMayNull, isPtrType, isVoidPtrType, isReadonly, isUnitType,
  mkU32Type, mkTupleType, mkUnboxed, mkFunType, getMemberType, getDerefType, getResultType,
  isUnboxedArrayMember, isUnboxedArrayDeref, tupleSize)
import Gencot.Cogent.Bindings (errVar, toDummyExpr, mkDummyExpr, isTakeBinding, isPutBindingFor, isTakePattern, isArrayTakePattern,
  mkUnitPattern, mkVarPattern, mkTuplePattern, mkVarTuplePattern)
import Gencot.Cogent.Expr (TypedVar(TV), typOfTV, mkUnitExpr, mkIntLitExpr, mkVarExpr, mkTupleExpr, mkVarTupleExpr,
  mkAppExpr, mkTopLevelFunExpr, mkMemberExpr, mkLambdaExpr, mkLetExpr)
import Gencot.Cogent.Post.Util (ETrav, freeInExpr, freeInPatn, freeInIrrefPatn,
  modifiedByBindings, varUsedIn, freeTypedVarsUnderBinding, boundTypedVarsInBindings)

{- Process take- and put-bindings -}
{- Detect and record errors.      -}
{----------------------------------}


tpproc :: GenExpr -> ETrav GenExpr
tpproc e = do
    e1 <- singletpproc e
    return $ tpmodify $ tpelim e1

-- | Process individual take- and put-bindings according to the container type.
-- If the container has MayNull type: error
-- If the container has abstract type: error
-- If the container has readonly type: convert take to member or getArr access.
-- If the container is the error variable: convert take to dummy binding for component variable.
-- If the component is cont for a record or array: error.
-- In all cases the put-binding is simply removed.
singletpproc :: GenExpr -> ETrav GenExpr
singletpproc (GenExpr (CS.Let bs bdy) o t c) = do
    bs' <- singletpprocBindings bs
    bdy' <- singletpproc bdy
    return $ GenExpr (CS.Let bs' bdy') o t c
singletpproc e =
    mapMExprOfGE (mapM singletpproc) e

singletpprocBindings :: [GenBnd] -> ETrav [GenBnd]
singletpprocBindings [] = return []
singletpprocBindings (b@(CS.Binding ip m e bvs) : bs)
    | (GenIrrefPatn (CS.PTake _ _) _ _) <- ip = do
        b' <- singletpprocTake b
        bs' <- singletpprocBindings bs
        return (b' : bs')
singletpprocBindings (b@(CS.Binding ip m e bvs) : bs)
    | (GenIrrefPatn (CS.PArrayTake _ _) _ _) <- ip = do
        b' <- singletpprocArrayTake b
        bs' <- singletpprocBindings bs
        return (b' : bs')
singletpprocBindings ((CS.Binding _ _ (GenExpr (CS.Put pv [Just (f,_)]) _ t _) _) : bs)
    | isMayNull t
      || isVoidPtrType t
      || isReadonly t
      || f == ptrDerivCompName && ((isUnitType mtype) || (mtype == mkUnboxed t))
    = singletpprocBindings bs
    where mtype = getMemberType f t
singletpprocBindings ((CS.Binding _ _ (GenExpr (CS.ArrayPut pv _) _ t _) _) : bs)
    | isMayNull t
      || isVoidPtrType t
      || isReadonly t
    = singletpprocBindings bs
singletpprocBindings ((CS.Binding ip m e bvs) : bs) = do
    e' <- singletpproc e
    bs' <- singletpprocBindings bs
    return ((CS.Binding ip m e' bvs) : bs')

singletpprocTake :: GenBnd -> ETrav GenBnd
singletpprocTake b@(CS.Binding ip m e bvs)
    | (GenIrrefPatn (CS.PTake pv [Just (f,cip)]) o t) <- ip =
    let (err,msg) =
            if f == ptrDerivCompName && (isArrayType t)
               then (False, "arrderef")
               else if isMayNull t
               then (True, "Dereferencing pointer which may be NULL")
               else if isVoidPtrType t
               then (True, "Dereferencing void pointer")
               else if isReadonly t
               then (False, "readonly")
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
       else if msg == "readonly"
       then return $ toNonLinAccess b
       else singletpprocArrayTake $ CS.Binding ipa m e bvs
singletpprocArrayTake :: GenBnd -> ETrav GenBnd
singletpprocArrayTake b@(CS.Binding ip _ e _)
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
       else return $ toNonLinAccess b

-- | Convert a take binding to a member access or application of getPtr or gerArr.
toNonLinAccess :: GenBnd -> GenBnd
toNonLinAccess (CS.Binding ip m e bvs)
    | (GenIrrefPatn (CS.PTake pv [Just (f,cip)]) o t) <- ip =
    let mtype = getMemberType f t
        mexpr = if isPtrType t
                   then mkAppExpr (mkTopLevelFunExpr ("getPtr", mkFunType t mtype) [Just t, Just mtype]) $ e
                   else mkMemberExpr mtype e f
    in CS.Binding cip Nothing mexpr []
toNonLinAccess (CS.Binding ip m e bvs)
    | (GenIrrefPatn (CS.PArrayTake pv [(idx,cip)]) _ t) <- ip =
    let etype = getDerefType t
        eexpr = mkAppExpr (mkTopLevelFunExpr ("getArr", mkFunType t etype) [Just t, Just mkU32Type, Just etype]) $ mkTupleExpr [e,idx]
    in CS.Binding cip Nothing eexpr []

-- | Eliminate take or put bindings.
-- A take binding can be eliminated if the old component value is not used.
-- A put binding can be eliminated if the component is not modified
-- and the take binding can be eliminated or converted to a member access,
-- so that it does not produce a taken type for the container.
tpelim :: GenExpr -> GenExpr
tpelim (GenExpr (CS.Let bs bdy) o t c) =
    GenExpr (CS.Let bs' bdy') o t c
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
         then tkb : (scp' ++ [ptb])
         else  scp' ++ [ptb]
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
          needPut = (elem cmp $ modifiedByBindings scp') || (not $ isNonlinear t) || (cmpIsUnboxedArray ip)

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

cmpIsUnboxedArray :: GenIrrefPatn -> Bool
cmpIsUnboxedArray (GenIrrefPatn (CS.PTake _ [Just (f,_)]) _ t) = isUnboxedArrayMember f t
cmpIsUnboxedArray (GenIrrefPatn (CS.PArrayTake _ _) _ t) = isUnboxedArrayDeref t


-- | Convert pairs of take and put bindings to modify applications.
tpmodify :: GenExpr -> GenExpr
tpmodify (GenExpr (CS.Let bs bdy) o t c) =
    GenExpr (CS.Let bs' bdy') o t c
    where bs' = tpmodifyInBindings bs bdy
          bdy' = tpmodify bdy
tpmodify e =
    mapExprOfGE (fmap tpmodify) e

tpmodifyInBindings :: [GenBnd] -> GenExpr -> [GenBnd]
tpmodifyInBindings [] bdy = []
tpmodifyInBindings (tkb@(CS.Binding ip _ _ _) : bs) bdy | isTakePattern ip =
    scp' ++ bs'
    where (cmp,scp,ptb,rst) = getTakePutScope tkb bs
          scp' = tpmodifyForTake False cmp tkb scp ptb rst bdy
          bs' = tpmodifyInBindings rst bdy
tpmodifyInBindings ((CS.Binding ip m e bvs) : bs) bdy =
    (CS.Binding ip m (tpmodify e) bvs) : (tpmodifyInBindings bs bdy)

-- | Process a pair of take and put bindings or arrayTake and arrayPut binding.
-- The result is the single binding for a modify application
-- or the binding sequence from take to put with processed nested take/put pairs.
-- The first argument is a flag to force the conversion to modify application.
-- The second argument is the taken component variable.
-- The following three arguments are the take binding, the bindings between take and put and the put binding.
-- The sixth argument is the list of bindings following the put binding.
-- The last argument is the let body following all bindings.
tpmodifyForTake :: Bool -> TypedVar -> GenBnd -> [GenBnd] -> GenBnd -> [GenBnd] -> GenExpr -> [GenBnd]
tpmodifyForTake force cmp@(TV cn ct) tkb@(CS.Binding ip _ _ _) scp ptb rst bdy =
    if doModif
       then [getModFunFromTake ip chfun inpvars outvars]
       else tkb : (scp' ++ [ptb])
    where doModif = force || isArrayTakePattern ip || cmpIsUnboxedArray ip
          (pre,nst) = break isTakeBinding scp -- nested take binding is first in nst
          scp' = if null nst
                    then pre
                    else let ntkb = head nst
                             (ncmp,nscp,nptb,nrst) = getTakePutScope ntkb (tail nst)
                             nscp' = tpmodifyForTake doModif ncmp ntkb nscp nptb (nrst ++ rst) bdy
                         in pre ++ nscp' ++ nrst
          outvars = filter (\(TV v _) -> varUsedIn v rst bdy) $ boundTypedVarsInBindings scp'
          chbdy = mkUnitTupleExpr cmp outvars
          inpvars = filter (\(TV v _) -> varUsedIn v scp' chbdy) $ freeTypedVarsUnderBinding (tkb : scp') (cmp: outvars)
          chargs = mkUnitTuplePattern cmp inpvars
          chfun = mkLambdaExpr chargs $ mkLetExpr scp' chbdy

getModFunFromTake :: GenIrrefPatn -> GenExpr -> [TypedVar] -> [TypedVar] -> GenBnd
getModFunFromTake (GenIrrefPatn (CS.PTake pv [Just (f,(GenIrrefPatn (CS.PVar cv) _ ct))]) _ t) chfun inpvars outvars =
    CS.Binding (mkUnitTuplePattern (TV pv t) outvars) Nothing (mkAppExpr modfun $ mkTupleExpr ([mkVarExpr $ TV pv t, chfun] ++ inpexprs)) []
    where modargtype = mkTupleType [ct, typOfGE chfun, inptype]
          modfuntype = mkFunType modargtype $ getResultType $ typOfGE chfun
          inptype = mkTupleType $ map typOfTV inpvars
          outtype = mkTupleType $ map typOfTV outvars
          inpexprs = if null inpvars
                        then [mkUnitExpr]
                        else map mkVarExpr inpvars
          modfun = mkTopLevelFunExpr ("modifyFld_" ++ f, modfuntype) [Just t, Just ct, Just inptype, Just outtype]
getModFunFromTake (GenIrrefPatn (CS.PArrayTake pv [(idx,(GenIrrefPatn (CS.PVar cv) _ ct))]) _ t) chfun inpvars outvars =
    CS.Binding (mkUnitTuplePattern  (TV pv t) outvars) Nothing (mkAppExpr modfun $ mkTupleExpr ([mkVarExpr $ TV pv t,idx,chfun] ++ inpexprs)) []
    where modargtype = mkTupleType [ct, mkU32Type, typOfGE chfun, inptype]
          modfuntype = mkFunType modargtype $ getResultType $ typOfGE chfun
          inptype = mkTupleType $ map typOfTV inpvars
          outtype = mkTupleType $ map typOfTV outvars
          inpexprs = if null inpvars
                        then [mkUnitExpr]
                        else map mkVarExpr inpvars
          modfun = mkTopLevelFunExpr ("modifyArr", modfuntype) [Just t, Just mkU32Type, Just ct, Just inptype, Just outtype]

mkUnitTuplePattern :: TypedVar -> [TypedVar] -> GenIrrefPatn
mkUnitTuplePattern v [] = mkTuplePattern [mkVarPattern v, mkUnitPattern]
mkUnitTuplePattern v vars = mkVarTuplePattern (v : vars)

mkUnitTupleExpr :: TypedVar -> [TypedVar] -> GenExpr
mkUnitTupleExpr v [] = mkTupleExpr [mkVarExpr v, mkUnitExpr]
mkUnitTupleExpr v vars = mkVarTupleExpr (v : vars)

