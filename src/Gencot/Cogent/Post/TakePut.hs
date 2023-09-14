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
  mkU32Type, mkUnboxed, mkFunType, getMemberType, getDerefType, isUnboxedArrayMember, isUnboxedArrayDeref)
import Gencot.Cogent.Bindings (errVar, toDummyExpr, mkDummyExpr, isTakeBinding, isPutBindingFor, isTakePattern)
import Gencot.Cogent.Expr (TypedVar(TV), mkIntLitExpr, mkTupleExpr, mkAppExpr, mkTopLevelFunExpr, mkMemberExpr)
import Gencot.Cogent.Post.Util (ETrav, freeInExpr, freeInIrrefPatn, modifiedByBindings)

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
-- The last argument is the let body.
tpelimForTake :: TypedVar -> GenBnd -> [GenBnd] -> GenBnd -> [GenBnd] -> GenExpr -> [GenBnd]
tpelimForTake (TV cmp ct) tkb@(CS.Binding _ _ (GenExpr _ _ t _) _) scp ptb rst bdy =
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
          needTake bs = (cmpUsedIn cmp bs bdy) || (not $ isNonlinear ct)
          needPut = (elem cmp $ modifiedByBindings scp') || (not $ isNonlinear t) || (cmpIsUnboxedArray tkb)

-- | Retrieve the scope of a take binding from a binding sequence.
-- The first argument is a take binding.
-- The result is the component variable, the binding sequence before the put, the put binding, and the binding sequence after the put.
getTakePutScope :: GenBnd -> [GenBnd] -> (TypedVar, [GenBnd], GenBnd, [GenBnd])
getTakePutScope tkb bs =
    (tv, scp, head rst, tail rst)
    where tv@(TV cmp ct) = getCmpVarFromTake tkb
          (scp,rst) = break (isPutBindingFor cmp) bs -- put binding is first in rst, must be present

cmpUsedIn :: CCS.VarName -> [GenBnd] -> GenExpr -> Bool
cmpUsedIn v [] e = elem v $ freeInExpr e
cmpUsedIn v ((CS.Binding (GenIrrefPatn (CS.PVar pv) _ _) _ e _) : bs) bdy | (elem v $ freeInExpr e) =
    cmpUsedIn pv bs bdy || cmpUsedIn v bs bdy
cmpUsedIn v ((CS.Binding ip _ e _) : bs) bdy =
    (elem v $ freeInExpr e) || ((not $ elem v $ freeInIrrefPatn ip) && (cmpUsedIn v bs bdy))

getCmpVarFromTake :: GenBnd -> TypedVar
getCmpVarFromTake (CS.Binding (GenIrrefPatn (CS.PTake _ [Just (_,(GenIrrefPatn (CS.PVar cv) _ ct))]) _ _) _ _ _) = TV cv ct
getCmpVarFromTake (CS.Binding (GenIrrefPatn (CS.PArrayTake _ [(_,(GenIrrefPatn (CS.PVar cv) _ ct))]) _ _) _ _ _) = TV cv ct

cmpIsUnboxedArray :: GenBnd -> Bool
cmpIsUnboxedArray (CS.Binding (GenIrrefPatn (CS.PTake _ [Just (f,_)]) _ t) _ _ _) = isUnboxedArrayMember f t
cmpIsUnboxedArray (CS.Binding (GenIrrefPatn (CS.PArrayTake _ _) _ t) _ _ _) = isUnboxedArrayDeref t


-- | Convert pairs of take and put bindings to modify applications.
tpmodify :: GenExpr -> GenExpr
tpmodify e = e
