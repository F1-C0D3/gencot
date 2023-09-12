{-# LANGUAGE PackageImports #-}
module Gencot.Cogent.Post.TakePut where

import Language.C.Data.Error
import Language.C.Analysis as LCA (Trav,recordError,getUserState,modifyUserState)

import Cogent.Surface as CS
import Cogent.Common.Syntax as CCS

import Gencot.Names (ptrDerivCompName)
import Gencot.Cogent.Ast
import Gencot.Cogent.Error (takeOp)
import Gencot.Cogent.Types (
  isUnsizedArrayType, isArrayType, isMayNull, isPtrType, isVoidPtrType, isReadonly, isUnitType,
  mkU32Type, mkUnboxed, mkFunType, getMemberType, getDerefType)
import Gencot.Cogent.Bindings (errVar, toDummyExpr, mkDummyExpr)
import Gencot.Cogent.Expr (mkIntLitExpr, mkTupleExpr, mkAppExpr, mkTopLevelFunExpr, mkMemberExpr)
import Gencot.Cogent.Post.Util

{- Process take- and put-bindings -}
{- Detect and record errors.      -}
{----------------------------------}


tpproc :: GenExpr -> ETrav GenExpr
tpproc e = do
    e1 <- singletpproc e
    pairtpproc e1

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
        mexpr = if isPtrType t
                   then mkAppExpr (mkTopLevelFunExpr ("getPtr", mkFunType t mtype) [Just t, Just mtype]) $ e
                   else mkMemberExpr mtype e f
        ipa = (GenIrrefPatn (CS.PArrayTake pv [(idx0,cip)]) o t)
        idx0 = mkIntLitExpr mkU32Type 0
    in if err
       then do
           recordError $ takeOp (orgOfGE e) msg
           return $ CS.Binding cip Nothing dummy []
       else if null msg
       then return b
       else if msg == "readonly"
       then return $ CS.Binding cip Nothing mexpr []
       else singletpprocArrayTake $ CS.Binding ipa m e bvs
singletpprocArrayTake :: GenBnd -> ETrav GenBnd
singletpprocArrayTake b@(CS.Binding ip m e bvs)
    | (GenIrrefPatn (CS.PArrayTake pv [(idx,cip)]) _ t) <- ip =
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
        etype = getDerefType t
        dummy = toDummyExpr e $ mkDummyExpr (typOfGIP cip) msg
        eexpr = mkAppExpr (mkTopLevelFunExpr ("getArr", mkFunType t etype) [Just t, Just mkU32Type, Just etype]) $ mkTupleExpr [e,idx]
    in if err
       then do
           recordError $ takeOp (orgOfGE e) msg
           return $ CS.Binding cip Nothing dummy []
       else if null msg
       then return b
       else return $ CS.Binding cip Nothing eexpr []


-- | Process pairs of take- and put-bindings with respect to bindings between them.
pairtpproc :: GenExpr -> ETrav GenExpr
pairtpproc e = return e
