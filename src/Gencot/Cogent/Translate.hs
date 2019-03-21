{-# LANGUAGE PackageImports #-}
module Gencot.Cogent.Translate where

import Control.Monad (liftM)

import "language-c" Language.C as LC hiding (pretty,Pretty)
import Language.C.Data.Ident as LCI
import Language.C.Data.Node as LCN
import Language.C.Data.Position as LCP
import Language.C.Analysis as LCA
import Language.C.Analysis.DefTable as LCD
import Language.C.Syntax.AST as LCS

import Cogent.Surface as CS
import Cogent.Common.Syntax as CCS
import Cogent.Common.Types as CCT
import Cogent.Util (ffmap)

import Gencot.Origin (Origin,noOrigin,origin,mkOrigin,noComOrigin)
import Gencot.Names (transTagName,transObjName,mapIfUpper,mapNameToUpper,mapNameToLower)
import Gencot.Cogent.Ast
import Gencot.C.Translate (transStat,transExpr,resolveTypedef,isAggregate)
import Gencot.Traversal (FTrav)

genType t = GenType t noOrigin

transGlobals :: [LCA.DeclEvent] -> FTrav [GenToplv]
transGlobals = mapM transGlobal

transGlobal :: LCA.DeclEvent -> FTrav GenToplv
transGlobal (LCA.TagEvent (LCA.CompDef (LCA.CompType sueref LCA.StructTag mems _ n))) = do
    tn <- transTagName $ LCA.TyComp $ LCA.CompTypeRef sueref LCA.StructTag n
    ms <- mapM transMember (aggBitfields mems)
    return $ GenToplv (CS.TypeDec tn [] $ genType $ CS.TRecord ms markBox) $ mkOrigin n
transGlobal (LCA.TagEvent (LCA.CompDef (LCA.CompType sueref LCA.UnionTag _ _ n))) = do
    tn <- transTagName $ LCA.TyComp $ LCA.CompTypeRef sueref LCA.UnionTag n
    return $ GenToplv (CS.AbsTypeDec tn [] []) $ mkOrigin n
transGlobal (LCA.TagEvent (LCA.EnumDef (LCA.EnumType sueref es _ n))) = do
    tn <- transTagName $ LCA.TyEnum $ LCA.EnumTypeRef sueref n
    return $ GenToplv (CS.TypeDec tn [] $ genType $ CS.TCon "U32" [] markUnbox) $ mkOrigin n
transGlobal (LCA.DeclEvent (LCA.FunctionDef (LCA.FunDef decl@(LCA.VarDecl (LCA.VarName idnam _) _ typ) stat n))) = do
    f <- transObjName idnam
    t <- transType typ
    ps <- transParamNames (if isVar then [] else pars)
    LCA.enterFunctionScope
    LCA.defineParams undefNode decl
    d <- dummyExpr res
    s <- transStat stat
    LCA.leaveFunctionScope
    return $ GenToplv (CS.FunDef f (CS.PT [] $ makeParReadOnly t) [CS.Alt ps CCS.Regular $ FunBody d s]) $ mkOrigin n
    where (LCA.FunctionType (LCA.FunType res pars isVar) _) = typ
transGlobal (LCA.DeclEvent (LCA.EnumeratorDef (LCA.Enumerator idnam expr _ n))) = do
    e <- transExpr expr
    return $ GenToplv (CS.ConstDef en (genType $ CS.TCon "U32" [] markUnbox) $ ConstExpr e) $ mkOrigin n
    where en = mapNameToLower idnam
transGlobal (LCA.TypeDefEvent (LCA.TypeDef idnam typ _ n)) = do
    t <- liftM (boxIf $ isAggregate $ resolveTypedef typ) $ transType typ
    return $ GenToplv (CS.TypeDec tn [] t) $ mkOrigin n
    where tn = mapNameToUpper idnam
transGlobal _ = return $ GenToplv (CS.Include "err-unexpected toplevel") noOrigin

makeParReadOnly (GenType (CS.TFun pt rt) o) = GenType (CS.TFun (genType $ CS.TBang pt) rt) o
makeParReadOnly t = t

aggBitfields :: [LCA.MemberDecl] -> [LCA.MemberDecl]
aggBitfields ms = foldl accu [] ms
    where accu :: [LCA.MemberDecl] -> LCA.MemberDecl -> [LCA.MemberDecl]
          accu [] md = [md]
          accu ms m@(LCA.MemberDecl _ Nothing _) = ms ++ [m]
          accu ms (LCA.MemberDecl _ (Just e) n) = procBitfield e ms n
          accu ms (LCA.AnonBitField _ e n) = procBitfield e ms n
          procBitfield :: LCS.CExpr -> [LCA.MemberDecl] -> LC.NodeInfo -> [LCA.MemberDecl]
          procBitfield e ms n =
              let lm = last ms in
                  if canAddTo lm e
                     then (init ms) ++ [addTo lm e]
                     else ms ++ [bitfieldgrp e ms n]
          canAddTo :: LCA.MemberDecl -> LCS.CExpr -> Bool
          canAddTo (LCA.MemberDecl _ (Just (LCS.CConst (LCS.CIntConst (LC.CInteger i1 _ _) _))) _)
            ((LCS.CConst (LCS.CIntConst (LC.CInteger i2 _ _) _))) = 
                i1 + i2 <= 32
          canAddTo _ _ = False
          addTo :: LCA.MemberDecl -> LCS.CExpr -> LCA.MemberDecl
          addTo (LCA.MemberDecl v (Just (LCS.CConst (LCS.CIntConst (LC.CInteger i1 r f) nn))) n)
            ((LCS.CConst (LCS.CIntConst (LC.CInteger i2 _ _) _))) = 
                (LCA.MemberDecl v (Just (LCS.CConst (LCS.CIntConst (LC.CInteger (i1+i2) r f) nn))) n)
          bitfieldgrp :: CExpr -> [LCA.MemberDecl] -> LC.NodeInfo -> LCA.MemberDecl
          bitfieldgrp e ms n = 
              LCA.MemberDecl 
                (LCA.VarDecl 
                    (LCA.VarName (LCI.Ident (grpnam ms) 0 LCN.undefNode) Nothing)
                    (LCA.DeclAttrs LCA.noFunctionAttrs LCA.NoStorage []) 
                    (LCA.DirectType (LCA.TyIntegral LCA.TyInt) LCA.noTypeQuals [])) (Just e) n
          grpnam :: [LCA.MemberDecl] -> String
          grpnam ms = "cogent_bitfield" ++ (show $ 1 + (length $ filter isBitfield ms))
          isBitfield (LCA.MemberDecl _ Nothing _) = False
          isBitfield _ = True

transMember :: LCA.MemberDecl -> FTrav (CCS.FieldName, (GenType, CS.Taken))
transMember (LCA.MemberDecl (LCA.VarDecl (LCA.VarName idnam _) att typ) _ n) = do
    t <- transType typ
    return (mapIfUpper idnam, ((GenType (typeOfGT t) $ mkOrigin n), False))
{- LCA.AnonBitField cannot occur since it is always replaced by aggBitfields -}

transParamNames :: [LCA.ParamDecl] -> FTrav GenIrrefPatn
transParamNames [] = return $ GenIrrefPatn CS.PUnitel noOrigin
transParamNames [pd] = transParamName pd
transParamNames pars = do
    ps <- mapM transParamName pars
    return $ GenIrrefPatn (CS.PTuple ps) noOrigin

transParamName :: LCA.ParamDecl -> FTrav GenIrrefPatn
transParamName pd = 
    return $ GenIrrefPatn (CS.PVar $ mapIfUpper idnam) $ noComOrigin pd
    where (LCA.VarDecl (LCA.VarName idnam _) _ _) = getVarDecl pd

transType :: LCA.Type -> FTrav GenType 
transType (LCA.DirectType TyVoid _ _) = 
    return $ GenType CS.TUnit noOrigin
transType (LCA.DirectType tnam quals _) = do
    t <- transTNam tnam
    return $ genType $ CS.TCon t [] 
        (case tnam of
             (LCA.TyComp _) -> markUnbox
             (LCA.TyEnum _) -> markUnbox
             _ -> markBox)
    where transTNam (LCA.TyComp _) = transTagName tnam
          transTNam (LCA.TyEnum (LCA.EnumTypeRef (AnonymousRef _) _)) = return "U32"
          transTNam (LCA.TyEnum _) = transTagName tnam
          transTNam (LCA.TyIntegral TyBool) =    return "todo-bool"
          transTNam (LCA.TyIntegral TyChar) =    return "U8"
          transTNam (LCA.TyIntegral TySChar) =   return "U8"
          transTNam (LCA.TyIntegral TyUChar) =   return "U8"
          transTNam (LCA.TyIntegral TyShort) =   return "U16"
          transTNam (LCA.TyIntegral TyUShort) =  return "U16"
          transTNam (LCA.TyIntegral TyInt) =     return "U32"
          transTNam (LCA.TyIntegral TyUInt) =    return "U32"
          transTNam (LCA.TyIntegral TyInt128) =  return "err-int128"
          transTNam (LCA.TyIntegral TyUInt128) = return "err-uint128"
          transTNam (LCA.TyIntegral TyLong) =    return "U64"
          transTNam (LCA.TyIntegral TyULong) =   return "U64"
          transTNam (LCA.TyIntegral TyLLong) =   return "U64"
          transTNam (LCA.TyIntegral TyULLong) =  return "U64"
          transTNam (LCA.TyFloating _) =         return "err-float"
          transTNam (LCA.TyComplex _) =          return "err-complex"
          transTNam (LCA.TyBuiltin _) =          return "err-builtin" 
transType (LCA.PtrType t quals _) | isFunction $ resolveTypedef t =
    transType t
transType (LCA.PtrType t quals _) | isAggregate $ resolveTypedef t =
    liftM setBoxed $ transType t
transType (LCA.PtrType t quals _) = liftM ptrType $ transType t
transType (LCA.ArrayType t _ quals _) = liftM arrType $ transType t
transType (LCA.FunctionType (LCA.FunType _ _ True) _) = errType "fun-varargs"
transType (LCA.FunctionType (LCA.FunTypeIncomplete _ ) _) = errType "fun-incompl"
transType (LCA.FunctionType (LCA.FunType ret pars False) _) = do
    r <- transType ret
    ps <- transParamTypes pars
    return $ genType $ CS.TFun ps r
transType (LCA.TypeDefType (LCA.TypeDefRef idnam typ _) quals _) =
    return $ boxIf (not $ isAggregate $ resolveTypedef typ) $ genType $ CS.TCon tn [] markUnbox
    where tn = mapNameToUpper idnam

ptrType :: GenType -> GenType
--ptrType t = GenType (CS.TCon "CPointerTo" [t] $ markBox) noOrigin
ptrType (GenType CS.TUnit o) = mkPtrType "CPointerTo_Void" o
ptrType (GenType (CS.TCon nam [] CCT.Unboxed) o) = mkPtrType "err-CPointerTo_Unboxed" o
ptrType (GenType (CS.TCon nam [] b) o) = mkPtrType ("CPointerTo_"++nam) o

mkPtrType :: String -> Origin -> GenType
mkPtrType nam = GenType (CS.TCon nam [] $ markBox)

arrType :: GenType -> GenType
--arrType t = GenType (CS.TUnbox $ GenType (CS.TCon "CArrayOf" [t] $ markBox) noOrigin) noOrigin
arrType (GenType CS.TUnit o) = mkArrType "err-CArrayOf_Void" o
arrType (GenType (CS.TCon nam [] CCT.Unboxed) o) = mkArrType ("CArrayOf_U_"++nam) o
arrType (GenType (CS.TCon nam [] b) o) = mkArrType ("CArrayOf_"++nam) o
arrType (GenType (CS.TFun ps r) o) = arrType $ funType r

mkArrType :: String -> Origin -> GenType
mkArrType nam = GenType (CS.TCon nam [] $ markUnbox)

funType :: GenType -> GenType
funType (GenType CS.TUnit o) = mkFunType "CFunRet_Void" o
funType (GenType (CS.TCon nam [] CCT.Unboxed) o) = mkFunType ("CFunRet_U_"++nam) o
funType (GenType (CS.TCon nam [] b) o) = mkArrType ("CFunRet_"++nam) o
funType (GenType (CS.TFun ps r) o) = funType $ funType r

mkFunType :: String -> Origin -> GenType
mkFunType nam = GenType (CS.TCon nam [] $ markBox)

transParamTypes :: [LCA.ParamDecl] -> FTrav GenType
transParamTypes [] = return $ genType CS.TUnit
transParamTypes [pd] = transParamType pd
transParamTypes pars = do
    ps <- mapM transParamType pars
    return $ genType $ CS.TTuple ps

transParamType :: LCA.ParamDecl -> FTrav GenType
transParamType pd = do
    t <- liftM (boxIf $ isArray $ resolveTypedef ptyp) $ transType ptyp
    return $ GenType (typeOfGT t) $ origin pd
    where (LCA.VarDecl _ _ ptyp) = getVarDecl pd

dummyExpr :: LCA.Type -> FTrav RawExpr
dummyExpr (LCA.DirectType TyVoid _ _) = 
    return $ CS.RE CS.Unitel
dummyExpr (LCA.DirectType tnam@(LCA.TyComp _) _ _) = do
    t <- transTagName tnam
    return $ dummyApp ("dummy_Unbox_" ++ t)
dummyExpr (LCA.DirectType tnam _ _) = do
    return $ CS.RE $ CS.IntLit 0
dummyExpr (LCA.PtrType (LCA.TypeDefType (LCA.TypeDefRef idnam typ _) _ _) _ _) | isAggregate $ resolveTypedef typ = do
    return $ dummyApp ("dummy_" ++ (mapNameToUpper idnam))
dummyExpr (LCA.PtrType (LCA.TypeDefType (LCA.TypeDefRef idnam typ _) _ _) _ _) | isFunction $ resolveTypedef typ = do
    return $ dummyApp ("dummy_" ++ (mapNameToUpper idnam))
dummyExpr (LCA.PtrType t _ _) | isFunction $ resolveTypedef t = do
    e <- dummyExpr ret
    return $ CS.RE $ CS.Lam (CS.RIP CS.PUnderscore) Nothing e
    where (LCA.FunctionType (LCA.FunType ret _ _) _) = resolveTypedef t
dummyExpr (LCA.PtrType t _ _) | isArray $ resolveTypedef t = do
    tp <- transType eltp
    return $ dummyArrApp tp
    where (LCA.ArrayType eltp _ _ _) = resolveTypedef t
dummyExpr (LCA.PtrType t _ _) | isAggregate $ resolveTypedef t = do
    t <- transTagName tnam
    return $ dummyApp ("dummy_" ++ t)
    where (LCA.DirectType tnam@(LCA.TyComp _) _ _) = resolveTypedef t
dummyExpr (LCA.PtrType t _ _) = do
    tp <- transType t
    return $ dummyPtrApp tp
dummyExpr (LCA.TypeDefType (LCA.TypeDefRef idnam typ _) _ _) = return $
    case rtyp of
         (LCA.DirectType (LCA.TyComp _) _ _) -> dummyApp ("dummy_Unbox_" ++ (mapNameToUpper idnam))
         (LCA.DirectType TyVoid _ _) -> CS.RE CS.Unitel
         (LCA.DirectType _ _ _) -> CS.RE $ CS.IntLit 0
         _ -> dummyApp ("dummy_" ++ (mapNameToUpper idnam))
    where rtyp = resolveTypedef typ

dummyAppExpr :: CS.RawExpr -> CS.RawExpr
dummyAppExpr fun = CS.RE $ CS.App fun (CS.RE CS.Unitel) False

dummyApp :: String -> CS.RawExpr
dummyApp fnam = dummyAppExpr $ CS.RE $ CS.Var fnam

dummyPtrApp :: GenType -> CS.RawExpr
dummyPtrApp (GenType CS.TUnit o) = dummyApp "dummy_Pointer_Void"
dummyPtrApp (GenType (CS.TCon nam [] CCT.Unboxed) o) = dummyApp ("err-dummy_Pointer_U_"++nam)
dummyPtrApp (GenType (CS.TCon nam [] b) o) = dummyApp ("dummy_Pointer_"++nam)

dummyArrApp :: GenType -> CS.RawExpr
dummyArrApp (GenType CS.TUnit o) = dummyApp "err-dummy_Array_Void"
dummyArrApp (GenType (CS.TCon nam [] CCT.Unboxed) o) = dummyApp ("dummy_Array_U_"++nam)
dummyArrApp (GenType (CS.TCon nam [] b) o) = dummyApp ("dummy_Array_"++nam)
dummyArrApp (GenType (CS.TFun ps r) o) = dummyArrApp $ funType r

--dummyPolyApp :: String -> GenType -> CS.RawExpr
--dummyPolyApp fnam typ = dummyAppExpr $ CS.RE $ CS.TypeApp fnam [Just $ stripOrigT typ] NoInline

isFunction :: LCA.Type -> Bool
isFunction (LCA.FunctionType _ _) = True
isFunction _ = False

isArray :: LCA.Type -> Bool
isArray (LCA.ArrayType _ _ _ _) = True
isArray _ = False

setBoxed :: GenType -> GenType
setBoxed (GenType (CS.TCon nam p _) o) = (GenType (CS.TCon nam p markBox) o)
setBoxed (GenType (CS.TUnbox (GenType t _)) o) = (GenType t o)

boxIf :: Bool -> GenType -> GenType
boxIf True t = setBoxed t
boxIf False t = t

markBox = CCT.Boxed False CS.noRepE
markUnbox = CCT.Unboxed

errType :: String -> FTrav GenType
errType s = return $ genType $ CS.TCon ("err-" ++ s) [] markUnbox

stripOrigT :: GenType -> RawType
stripOrigT = RT . fmap stripOrigT . ffmap (const $ CS.RE CS.Unitel) . typeOfGT
