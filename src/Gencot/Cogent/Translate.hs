{-# LANGUAGE PackageImports #-}
module Gencot.Cogent.Translate where

import Control.Monad (liftM,when)
import Data.List (nub)
import Data.Map (Map,singleton,unions,toList)
import Data.Maybe (catMaybes)

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
import Gencot.Names (transTagName,transObjName,mapIfUpper,mapNameToUpper,mapNameToLower,mapPtrDeriv,mapArrDeriv,mapFunDeriv,mapParmodDeriv,mkDerivedName,mkParTypeName,srcFileName)
import Gencot.Cogent.Ast
import Gencot.C.Translate (transStat,transExpr)
import Gencot.Traversal (FTrav,getParmods)
import Gencot.Util.Types (getDerivedParts,usedTypeNames,resolveFully,isExtern,isAggOrFunc,isAggPointer,isNamedFunPointer,isFunPointer,isFunction,isArray,resolveTypedef,isAggregate,isLinearParType,isReadOnlyParType,wrapFunAsPointer)
import Gencot.Json.Identifier (getFunId,getFunMemberId,getFunTypeId,getLocalFunId,carriedWithFunIds)

genType t = GenType t noOrigin

transGlobals :: [LCA.DeclEvent] -> FTrav [GenToplv]
transGlobals = mapM transGlobal

transGlobal :: LCA.DeclEvent -> FTrav GenToplv
transGlobal (LCA.TagEvent (LCA.CompDef (LCA.CompType sueref LCA.StructTag mems _ n))) = do
    tn <- transTagName $ LCA.TyComp $ LCA.CompTypeRef sueref LCA.StructTag n
    ms <- mapM (transMember sueref) (aggBitfields mems)
    return $ GenToplv (CS.TypeDec tn [] $ genType $ CS.TRecord ms markBox) $ mkOrigin n
transGlobal (LCA.TagEvent (LCA.CompDef (LCA.CompType sueref LCA.UnionTag _ _ n))) = do
    tn <- transTagName $ LCA.TyComp $ LCA.CompTypeRef sueref LCA.UnionTag n
    return $ GenToplv (CS.AbsTypeDec tn [] []) $ mkOrigin n
transGlobal (LCA.TagEvent (LCA.EnumDef (LCA.EnumType sueref es _ n))) = do
    tn <- transTagName $ LCA.TyEnum $ LCA.EnumTypeRef sueref n
    return $ GenToplv (CS.TypeDec tn [] $ genType $ CS.TCon "U32" [] markUnbox) $ mkOrigin n
transGlobal (LCA.DeclEvent (LCA.Declaration decl@(LCA.Decl (LCA.VarDecl (LCA.VarName idnam _) _ typ) n))) = do
    f <- transObjName idnam
    fid <- parmodFunId decl
    t <- transType fid typ
    t <- applyParmods [] fid t
    return $ GenToplv (CS.AbsDec f (CS.PT [] $ mkFunType t)) $ mkOrigin n
transGlobal (LCA.DeclEvent (LCA.FunctionDef fdef@(LCA.FunDef decl@(LCA.VarDecl (LCA.VarName idnam _) _ typ) stat n))) = do
    f <- transObjName idnam
    fid <- parmodFunId fdef
    t <- transType fid typ
    defaultParmods <- mapM mkDefaultParmod $ map LCA.declType pars
    t <- applyParmods defaultParmods fid t
    ps <- transParamNames pars
    LCA.enterFunctionScope
    LCA.defineParams LCN.undefNode decl
    d <- dummyExpr res
    d <- extendExpr fdef d pars
    s <- transStat stat
    LCA.leaveFunctionScope
    return $ GenToplv (CS.FunDef f (CS.PT [] t) [CS.Alt ps CCS.Regular $ FunBody d s]) $ mkOrigin n
    where (LCA.FunctionType (LCA.FunType res vpars isVar) _) = typ
          pars = (if isVar then [] else vpars)
transGlobal (LCA.DeclEvent odef@(LCA.ObjectDef (LCA.ObjDef decl@(LCA.VarDecl (LCA.VarName idnam _) _ typ) _ n))) = do
    f <- transObjName idnam
    fid <- parmodFunId odef
    t <- transType fid typ
    return $ GenToplv (CS.AbsDec f (CS.PT [] $ mkFunType t)) $ mkOrigin n
transGlobal (LCA.DeclEvent (LCA.EnumeratorDef (LCA.Enumerator idnam expr _ n))) = do
    e <- transExpr expr
    return $ GenToplv (CS.ConstDef en (genType $ CS.TCon "U32" [] markUnbox) $ ConstExpr e) $ mkOrigin n
    where en = mapNameToLower idnam
transGlobal (LCA.TypeDefEvent td@(LCA.TypeDef idnam typ _ n)) = do
    t <- transType (getFunTypeId td) modiftyp
    return $ GenToplv (CS.TypeDec tn [] t) $ mkOrigin n
    where tn = mapNameToUpper idnam
          modiftyp = if isAggOrFunc typ then (LCA.PtrType typ LCA.noTypeQuals [])
                                        else typ
transGlobal _ = return $ GenToplv (CS.Include "err-unexpected toplevel") noOrigin

transExtGlobals :: [String] -> [LCA.DeclEvent] -> FTrav [GenToplv]
transExtGlobals tds tcs = mapM (transExtGlobal tds) tcs

transExtGlobal :: [String] -> LCA.DeclEvent -> FTrav GenToplv
transExtGlobal tds (LCA.TypeDefEvent td@(LCA.TypeDef idnam typ _ n)) = do
    t <- transType (getFunTypeId td) restyp
    return $ GenToplv (CS.TypeDec tn [] t) $ mkOrigin n
    where tn = mapNameToUpper idnam
          restyp = resolveFully tds modiftyp
          modiftyp = if isAggOrFunc typ then (LCA.PtrType typ LCA.noTypeQuals [])
                                        else typ
transExtGlobal tds (LCA.TagEvent (LCA.CompDef (LCA.CompType sueref LCA.StructTag mems _ n))) = do
    tn <- transTagName $ LCA.TyComp $ LCA.CompTypeRef sueref LCA.StructTag n
    ms <- mapM (transExtMember tds sueref) (aggBitfields mems)
    return $ GenToplv (CS.TypeDec tn [] $ genType $ CS.TRecord ms markBox) $ mkOrigin n
transExtGlobal _ e = transGlobal e

genTypeDefs :: [String] -> [LCA.DeclEvent] -> FTrav [GenToplv]
genTypeDefs tds tcs = do
    derivedTypes <- liftM (unions . concat) $ mapM (genDerivedTypeNames tds) tcs
    liftM concat $ mapM (uncurry genDerivedTypeDefs) $ toList derivedTypes

genDerivedTypeNames :: [String] -> LCA.DeclEvent -> FTrav [Map String (String,LCA.Type)]
genDerivedTypeNames tdn tc = do
    sfn <- srcFileName tc
    liftM (map (\(gt,fid,t) -> singleton (getName gt) (fid,t))) $ 
        mapM (\(fid,t) -> do gt <- transType fid t; return (gt,fid,t)) $ 
        filter (\(_,t) -> not $ (isAggPointer t || isNamedFunPointer t)) $ 
        nub $ map (\(fid,t) -> (fid,wrapFunAsPointer t)) $ 
        concat $ map (uncurry getDerivedParts) $ carriedWithFunIds sfn tdn tc
    where getName (GenType (CS.TCon nam [] _) _) = nam

genDerivedTypeDefs :: String -> (String,LCA.Type) -> FTrav [GenToplv]
genDerivedTypeDefs nam (fid,(LCA.PtrType t _ _)) | not $ isFunction t = do
    gt <- transType "" t
    return $ [GenToplv (CS.TypeDec nam [] $ genType $ CS.TRecord [("cont", (gt, False))] markBox) noOrigin]
genDerivedTypeDefs nam (fid,(LCA.PtrType ftyp@(LCA.FunctionType (LCA.FunType ret pars False) _) _ _)) = do
    t <- transType fid ftyp
    defaultParmods <- mapM mkDefaultParmod $ map LCA.declType pars
    t <- applyParmods defaultParmods fid t
    let f_to = GenToplv (CS.AbsDec ("to_" ++ nam) (CS.PT [] $ genType $ CS.TFun t fptyp)) noOrigin
    let f_invk = GenToplv (CS.AbsDec ("invk_" ++ nam) (CS.PT [] $ prepPar fptyp t )) noOrigin
    return $ [tdef,f_to,f_invk]
    where tdef = GenToplv (CS.AbsTypeDec nam [] []) noOrigin
          fptyp = genType $ CS.TCon nam [] markUnbox
          prepPar fptyp (GenType (CS.TFun pt rt) o) = GenType (CS.TFun (pPar fptyp pt) rt) o
          pPar fptyp (GenType CS.TUnit o) = fptyp
          pPar fptyp (GenType (CS.TTuple ts) o) = (GenType (CS.TTuple (fptyp : ts)) o)
          pPar fptyp t = (GenType (CS.TTuple [fptyp,t]) noOrigin)
-- Pointer to aggregate and pointer to named function are suppressed in genDerivedTypeNames
-- Pointer to incomplete function or to variadic function are ???
genDerivedTypeDefs nam (fid,t) = 
    return $ [GenToplv (CS.AbsTypeDec nam [] []) noOrigin]

parmodFunId :: (LCA.Declaration d, LCN.CNode d) => d -> FTrav String
parmodFunId fdef = do
    sfn <- srcFileName $ LCA.declIdent fdef
    return $ getFunId fdef sfn

applyParmods :: [String] -> String -> GenType -> FTrav GenType
applyParmods dpms fid (GenType (CS.TFun pt rt) o) = do
    pms <- getParmods fid
    let hpms = if (length pms) < (length ptl) then dpms else pms
    let pts = zip hpms ptl
    return $ GenType (CS.TFun (applyToPars pts) (applyToRes pts rt)) o
    where ptl = ptlist pt
          ptlist (GenType CS.TUnit _) = []
          ptlist (GenType (CS.TTuple ts) _) = ts
          ptlist gt = [gt]
applyParmods _ _ t = return t

applyToPars :: [(String,GenType)] -> GenType
applyToPars pts = mkGenType $ map applyToPar pts

applyToPar :: (String,GenType) -> GenType
applyToPar (s,gt) | s == "readonly" || s == "no" = genType $ CS.TBang gt
applyToPar (_,gt) = gt

applyToRes :: [(String,GenType)] -> GenType -> GenType
applyToRes pts rt = mkGenType $ addrps rt
    where rps = map snd $ filter (((==) "yes") . fst) pts
          addrps (GenType CS.TUnit _) = rps
          addrps t = t : rps

extendExpr :: LCA.FunDef -> RawExpr -> [LCA.ParamDecl] -> FTrav RawExpr
extendExpr fdef e pars = do
    sfn <- srcFileName $ LCA.declIdent fdef
    pms <- getParmods $ getFunId fdef sfn
    let res = map (CS.RE . CS.Var . mapIfUpper . LCA.declIdent . snd) $ filter (((==) "yes") . fst) $ zip pms pars
    return $ mkRawExpr $ addres res e
    where addres res (CS.RE CS.Unitel) = res
          addres res e = e : res

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

transMember :: LCI.SUERef -> LCA.MemberDecl -> FTrav (CCS.FieldName, (GenType, CS.Taken))
transMember sueref mdecl@(LCA.MemberDecl (LCA.VarDecl (LCA.VarName idnam _) att typ) _ n) = do
    t <- transType (getFunMemberId sueref mdecl) typ
    return (mapIfUpper idnam, ((GenType (typeOfGT t) $ mkOrigin n), False))
{- LCA.AnonBitField cannot occur since it is always replaced by aggBitfields -}

transExtMember :: [String] -> LCI.SUERef -> LCA.MemberDecl -> FTrav (CCS.FieldName, (GenType, CS.Taken))
transExtMember tds sueref mdecl@(LCA.MemberDecl (LCA.VarDecl (LCA.VarName idnam _) att typ) _ n) = do
    t <- transType (getFunMemberId sueref mdecl) (resolveFully tds typ)
    return (mapIfUpper idnam, ((GenType (typeOfGT t) $ mkOrigin n), False))

transParamNames :: [LCA.ParamDecl] -> FTrav GenIrrefPatn
transParamNames [] = return $ GenIrrefPatn CS.PUnitel noOrigin
transParamNames [pd] = transParamName pd
transParamNames pars = do
    ps <- mapM transParamName pars
    return $ GenIrrefPatn (CS.PTuple ps) noOrigin

transParamName :: LCA.ParamDecl -> FTrav GenIrrefPatn
transParamName pd = 
    return $ GenIrrefPatn (CS.PVar $ mapIfUpper $ LCA.declIdent pd) $ noComOrigin pd

-- The first parameter is the function identifier to be used to retrieve a parmod description for 
-- a contained derived function type, or "" if no parmod description shall be used.
transType :: String -> LCA.Type -> FTrav GenType 
transType _ (LCA.DirectType TyVoid _ _) = 
    return $ genType CS.TUnit
transType fid (LCA.FunctionType (LCA.FunType ret pars variadic) _) = do
    r <- transType "" ret
    ps <- transParamTypes variadic fid pars
    return $ genType $ CS.TFun ps r
transType fid t = do
    (u,d,b) <- transDerivedType fid t
    return $ genType $ CS.TCon (mkDerivedName d b) [] $
        if u || isFunPointer t then markUnbox
                               else markBox

-- For first parameter see transType.
-- Bool is whether the unbox operator must be applied
-- 1st String is the encoding of all derivation steps
-- 2nd String is the name for the base type
transDerivedType :: String -> LCA.Type -> FTrav (Bool,String,String)
transDerivedType _ (LCA.DirectType TyVoid _ _) = 
    return (False,"","Void")
transDerivedType _ (LCA.DirectType tnam quals _) = do
    t <- transTNam tnam
    return (u,"",t)
    where u = case tnam of
                (LCA.TyComp _) -> True
                _ -> False
          transTNam (LCA.TyComp _) = transTagName tnam
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
transDerivedType fid (LCA.PtrType t quals _) = do
    (u,d,b) <- transDerivedType fid t
    if u then return (False,d,b)
         else return (False,mapPtrDeriv ++ d,b)
transDerivedType fid (LCA.ArrayType t as quals _) = do
    (u,d,b) <- transDerivedType fid t
    return (True,(mapArrDeriv as) ++ d,b)
transDerivedType fid (LCA.FunctionType ft _) = do
    (u,d,b) <- transDerivedType "" $ resultType ft
    pts <- mapM (transDerivedType "") $ map adjustParamType $ parTypes ft
    defaultParmods <- mapM mkDefaultParmod $ parTypes ft
    pts <- applyParmodsDerived defaultParmods fid pts
    return (True,(mapFunDeriv ft pts) ++ d,b)
    where resultType (LCA.FunType t _ _) = t
          resultType (LCA.FunTypeIncomplete t ) = t
          parTypes (LCA.FunType _ pts _) = map ((\(LCA.VarDecl _ _ ptyp) -> ptyp) . getVarDecl) pts
          parTypes (LCA.FunTypeIncomplete _) = []
transDerivedType _ (LCA.TypeDefType (LCA.TypeDefRef idnam typ _) quals _) =
    return (isAggOrFunc typ,"",tn)
    where tn = mapNameToUpper idnam

applyParmodsDerived :: [String] -> String -> [(Bool,String,String)] -> FTrav [(Bool,String,String)]
applyParmodsDerived dpms fid pts = do
    pms <- getParmods fid
    let hpms = if (length pms) < (length pts) then dpms else pms
    return $ map (\(pm, (u,d,b)) -> (u, (mapParmodDeriv pm) ++ d, b)) $ zip hpms pts

mkDefaultParmod :: LCA.Type -> FTrav String
mkDefaultParmod t = do
    lin <- isLinearParType t
    if not lin
       then return "nonlinear"
       else do
           ro <- isReadOnlyParType t
           if ro then return "readonly"
           else return "yes"

ptrType :: GenType -> GenType
--ptrType t = GenType (CS.TCon "CPointerTo" [t] $ markBox) noOrigin
ptrType (GenType CS.TUnit o) = mkBoxedType "CPointerTo_Void" o
ptrType (GenType (CS.TCon nam [] CCT.Unboxed) o) = mkBoxedType "err-CPointerTo_Unboxed" o
ptrType (GenType (CS.TCon nam [] b) o) = mkBoxedType ("CPointerTo_"++nam) o

mkBoxedType :: String -> Origin -> GenType
mkBoxedType nam = GenType (CS.TCon nam [] $ markBox)

arrType :: GenType -> GenType
--arrType t = GenType (CS.TUnbox $ GenType (CS.TCon "CArrayOf" [t] $ markBox) noOrigin) noOrigin
arrType (GenType CS.TUnit o) = mkUnboxedType "err-CArrayOf_Void" o
arrType (GenType (CS.TCon nam [] CCT.Unboxed) o) = mkUnboxedType ("CArrayOf_U_"++nam) o
arrType (GenType (CS.TCon nam [] b) o) = mkUnboxedType ("CArrayOf_"++nam) o
arrType (GenType (CS.TFun ps r) o) = arrType $ funType r

mkUnboxedType :: String -> Origin -> GenType
mkUnboxedType nam = GenType (CS.TCon nam [] $ markUnbox)

funType :: GenType -> GenType
funType (GenType CS.TUnit o) = mkBoxedType "CFunRet_Void" o
funType (GenType (CS.TCon nam [] CCT.Unboxed) o) = mkBoxedType ("CFunRet_U_"++nam) o
funType (GenType (CS.TCon nam [] b) o) = mkUnboxedType ("CFunRet_"++nam) o
funType (GenType (CS.TFun ps r) o) = funType $ funType r

mkFunType :: GenType -> GenType
mkFunType t@(GenType (CS.TFun _ _) _) = t
mkFunType t = genType $ CS.TFun (mkGenType []) t

-- The second argument is the parmod function identifier of the parameters' function.
transParamTypes :: Bool -> String -> [LCA.ParamDecl] -> FTrav GenType
transParamTypes variadic fid pars = do
    ps <- mapM (transParamType fid) pars
    return $ mkGenType (ps ++ if variadic then [variadicType] else [])

variadicType = genType (CS.TCon "Variadic_Cogent_Parameters" [] markBox)

transParamType :: String -> LCA.ParamDecl -> FTrav GenType
transParamType fid pd = do
    t <- transType (getLocalFunId fid pd) $ adjustParamType ptyp
    return $ GenType (typeOfGT t) $ origin pd
    where (LCA.VarDecl _ _ ptyp) = getVarDecl pd

adjustParamType :: LCA.Type -> LCA.Type
adjustParamType t | isArray t = (LCA.PtrType elt quals attrs)
    where (LCA.ArrayType elt _ quals attrs) = resolveTypedef t
adjustParamType t | isFunction t = (LCA.PtrType t LCA.noTypeQuals LCA.noAttributes)
adjustParamType t = t

dummyExpr :: LCA.Type -> FTrav RawExpr
dummyExpr (LCA.DirectType TyVoid _ _) = 
    return $ CS.RE CS.Unitel
dummyExpr (LCA.DirectType tnam@(LCA.TyComp _) _ _) = do
    t <- transTagName tnam
    return $ dummyApp ("dummy_Unbox_" ++ t)
dummyExpr (LCA.DirectType tnam _ _) = do
    return $ CS.RE $ CS.IntLit 0
dummyExpr (LCA.PtrType (LCA.TypeDefType (LCA.TypeDefRef idnam typ _) _ _) _ _) | isAggregate typ = do
    return $ dummyApp ("dummy_" ++ (mapNameToUpper idnam))
dummyExpr (LCA.PtrType (LCA.TypeDefType (LCA.TypeDefRef idnam typ _) _ _) _ _) | isFunction typ = do
    return $ dummyApp ("dummy_" ++ (mapNameToUpper idnam))
dummyExpr (LCA.PtrType t _ _) | isFunction t = do
    e <- dummyExpr ret
    return $ CS.RE $ CS.Lam (CS.RIP CS.PUnderscore) Nothing e
    where (LCA.FunctionType (LCA.FunType ret _ _) _) = resolveTypedef t
dummyExpr (LCA.PtrType t _ _) | isArray t = do
    tp <- transType ""{-todo-} eltp
    return $ dummyArrApp tp
    where (LCA.ArrayType eltp _ _ _) = resolveTypedef t
dummyExpr (LCA.PtrType t _ _) | isAggregate t = do
    t <- transTagName tnam
    return $ dummyApp ("dummy_" ++ t)
    where (LCA.DirectType tnam@(LCA.TyComp _) _ _) = resolveTypedef t
dummyExpr (LCA.PtrType t _ _) = do
    tp <- transType ""{-todo-} t
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

mkGenType :: [GenType] -> GenType
mkGenType [] = genType CS.TUnit
mkGenType [gt] = gt
mkGenType gts = genType $ CS.TTuple gts 

mkRawExpr :: [RawExpr] -> RawExpr
mkRawExpr [] = CS.RE CS.Unitel
mkRawExpr [re] = re
mkRawExpr res = CS.RE $ CS.Tuple res

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

