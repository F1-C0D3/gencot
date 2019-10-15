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

import Gencot.Origin (Origin,noOrigin,origin,mkOrigin,noComOrigin,mkBegOrigin,mkEndOrigin,prepOrigin,appdOrigin,isNested)
import Gencot.Names (transTagName,transObjName,mapIfUpper,mapNameToUpper,mapNameToLower,mapPtrDeriv,mapArrDeriv,mkNonLin,mapFunDeriv,mapParmodDeriv,mkDerivedName,mkParTypeName,srcFileName)
import Gencot.Cogent.Ast
import Gencot.C.Translate (transStat,transExpr)
import Gencot.Traversal (FTrav,getParmods,markTagAsNested,isMarkedAsNested)
import Gencot.Util.Types (getDerivedParts,usedTypeNames,resolveFully,isExtern,isCompOrFunc,isCompPointer,isNamedFunPointer,isFunPointer,isFunction,isComplete,isArray,isTagRef,containsTypedefs,resolveTypedef,isComposite,isLinearType,isLinearParType,isReadOnlyType,isReadOnlyParType,wrapFunAsPointer,getTagDef)
import Gencot.Json.Identifier (getFunId,getFunMemberId,getFunTypeId,getLocalFunId,carriedWithFunIds)

genType t = GenType t noOrigin

transGlobals :: [LCA.DeclEvent] -> FTrav [GenToplv]
transGlobals tcs = liftM concat $ mapM transGlobal tcs

transGlobal :: LCA.DeclEvent -> FTrav [GenToplv]
transGlobal (LCA.TagEvent (LCA.CompDef ct@(LCA.CompType _ LCA.StructTag _ _ _))) =
    transStruct ct transMember
transGlobal (LCA.TagEvent (LCA.CompDef (LCA.CompType sueref LCA.UnionTag _ _ n))) = do
    nst <- isMarkedAsNested sueref
    if nst 
       then return []
       else do
           tn <- transTagName $ LCA.TyComp $ LCA.CompTypeRef sueref LCA.UnionTag n
           return $ [GenToplv (CS.AbsTypeDec tn [] []) $ mkOrigin n]
transGlobal (LCA.TagEvent (LCA.EnumDef (LCA.EnumType sueref es _ n))) = do
    nst <- isMarkedAsNested sueref
    if nst || LCI.isAnonymousRef sueref
       then return []
       else do
           tn <- transTagName $ LCA.TyEnum $ LCA.EnumTypeRef sueref n
           return $ [GenToplv (CS.TypeDec tn [] $ genType $ CS.TCon "U32" [] markUnbox) $ mkOrigin n]
transGlobal (LCA.DeclEvent (LCA.Declaration decl@(LCA.Decl _ n))) | isComplete typ = do
    f <- transObjName $ LCA.declIdent decl
    fid <- parmodFunId decl
    t <- transType fid typ
    t <- applyParmods typ fid t
    return $ [GenToplv (CS.AbsDec f (CS.PT [] $ mkFunType t)) $ mkOrigin n]
    where typ = LCA.declType decl
          (LCA.FunctionType (LCA.FunType res vpars isVar) _) = typ
transGlobal (LCA.DeclEvent (LCA.FunctionDef fdef@(LCA.FunDef decl stat n))) = do
    f <- transObjName $ LCA.declIdent decl
    fid <- parmodFunId fdef
    t <- transType fid typ
    t <- applyParmods typ fid t
    ps <- transParamNames isVar pars
    LCA.enterFunctionScope
    LCA.defineParams LCN.undefNode decl
    d <- dummyExpr res
    d <- extendExpr fdef d pars
    s <- transStat stat
    LCA.leaveFunctionScope
    return $ [GenToplv (CS.FunDef f (CS.PT [] t) [CS.Alt ps CCS.Regular $ FunBody d s]) $ mkOrigin n]
    where typ = LCA.declType decl
          (LCA.FunctionType (LCA.FunType res pars isVar) _) = typ
transGlobal (LCA.DeclEvent odef@(LCA.ObjectDef (LCA.ObjDef decl@(LCA.VarDecl (LCA.VarName idnam _) _ typ) _ n))) = do
    f <- transObjName idnam
    fid <- parmodFunId odef
    t <- transType fid typ
    return $ [GenToplv (CS.AbsDec f (CS.PT [] $ mkFunType t)) $ mkOrigin n]
transGlobal (LCA.DeclEvent (LCA.EnumeratorDef (LCA.Enumerator idnam expr _ n))) = do
    e <- transExpr expr
    return $ [GenToplv (CS.ConstDef en (genType $ CS.TCon "U32" [] markUnbox) $ ConstExpr e) $ mkOrigin n]
    where en = mapNameToLower idnam

-- | Translate a typedef of the form
-- > typedef type-specifier declarator;
-- where @declarator@ denotes a (derived type for an) identifier @idnam@.
-- If the @type-specifier@ denotes a function, struct or union type the typedef is first adjusted
-- by replacing @idnam@ by @*idnam@, i.e. the typedef name is defined for a pointer to
-- function, struct, or union type.
-- 
-- The translation result has the form
-- > type idnam = type
-- where @type@ is constructed by translating @type-specifier@ and applying all derivations from the adjusted @declarator@.
transGlobal (LCA.TypeDefEvent td@(LCA.TypeDef idnam typ _ n)) = do
    t <- transType (getFunTypeId td) modiftyp
    nt <- transTagIfNested typ n
    return $ wrapOrigin n (nt ++ [GenToplv (CS.TypeDec tn [] t) noOrigin])
    where tn = mapNameToUpper idnam
          modiftyp = if isCompOrFunc typ then (LCA.PtrType typ LCA.noTypeQuals [])
                                         else typ
transGlobal _ = return $ [GenToplv (CS.Include "err-unexpected toplevel") noOrigin]

transExtGlobals :: [String] -> [LCA.DeclEvent] -> FTrav [GenToplv]
transExtGlobals tds tcs = liftM concat $ mapM (transExtGlobal tds) tcs

transExtGlobal :: [String] -> LCA.DeclEvent -> FTrav [GenToplv]
transExtGlobal tds (LCA.TypeDefEvent td@(LCA.TypeDef idnam typ _ n)) = do
    t <- transType (getFunTypeId td) restyp
    nt <- transTagIfNested typ n
    let o = if null nt then mkOrigin n else mkEndOrigin n
    return $ nt ++ [GenToplv (CS.TypeDec tn [] t) o]
    where tn = mapNameToUpper idnam
          restyp = resolveFully tds modiftyp
          modiftyp = if isCompOrFunc typ then (LCA.PtrType typ LCA.noTypeQuals [])
                                         else typ
transExtGlobal tds (LCA.TagEvent (LCA.CompDef ct@(LCA.CompType _ LCA.StructTag _ _ _))) = 
    transStruct ct (transExtMember tds)
transExtGlobal _ e = transGlobal e

transStruct :: LCA.CompType -> (LCI.SUERef -> LCA.MemberDecl -> FTrav (CCS.FieldName, (GenType, CS.Taken))) -> FTrav [GenToplv]
transStruct (LCA.CompType sueref LCA.StructTag mems _ n) trMember = do
    nst <- isMarkedAsNested sueref
    if nst 
       then return []
       else do
           tn <- transTagName $ LCA.TyComp $ LCA.CompTypeRef sueref LCA.StructTag n
           ms <- mapM (trMember sueref) aggmems
           nts <- liftM concat $ mapM transMemTagIfNested aggmems
           --let ttyp = genType $ CS.TTake Nothing $ genType $ CS.TCon tn [] markBox
           --let f_create = GenToplv (CS.AbsDec ("create_" ++ tn) (CS.PT [] $ genType $ CS.TFun utyp ttyp)) noOrigin
           --let f_dispose = GenToplv (CS.AbsDec ("dispose_" ++ tn) (CS.PT [] $ genType $ CS.TFun ttyp utyp)) noOrigin
           return $ wrapOrigin n ([GenToplv (CS.TypeDec tn [] $ genType $ CS.TRecord ms markBox) noOrigin{-,f_create,f_dispose-}] ++ nts)
    where utyp = genType CS.TUnit
          aggmems = aggBitfields mems

transMemTagIfNested :: LCA.MemberDecl -> FTrav [GenToplv]
transMemTagIfNested mdecl = transTagIfNested (LCA.declType mdecl) $ LCN.nodeInfo mdecl

transTagIfNested :: LCA.Type -> NodeInfo -> FTrav [GenToplv]
transTagIfNested typ@(LCA.DirectType tn _ _) n | isTagRef typ = do
    dt <- getDefTable
    let mtd = getTagDef dt $ getSUERef tn
    case mtd of
         Nothing -> return []
         Just td -> 
            if isNested (nodeInfo td) n 
               then do
                   ng <- transGlobal $ LCA.TagEvent td
                   markTagAsNested $ sueRef td
                   return ng
               else return []
    where getSUERef (LCA.TyComp r) = sueRef r
          getSUERef (LCA.TyEnum r) = sueRef r
transTagIfNested _ _ = return []

wrapOrigin :: LCN.NodeInfo -> [GenToplv] -> [GenToplv]
wrapOrigin n [] = []
wrapOrigin n [GenToplv t o] = [GenToplv t $ prepOrigin n $ appdOrigin n o]
wrapOrigin n gts = (GenToplv t1 $ prepOrigin n o1):((init $ tail gts)++[GenToplv t2 $ appdOrigin n o2])
    where (GenToplv t1 o1) = head gts
          (GenToplv t2 o2) = last gts

genTypeDefs :: [String] -> [LCA.DeclEvent] -> FTrav [GenToplv]
genTypeDefs tds tcs = do
    derivedTypes <- liftM (unions . concat) $ mapM (genDerivedTypeNames tds) tcs
    liftM concat $ mapM (uncurry genDerivedTypeDefs) $ toList derivedTypes

-- | Construct all names of derived types occurring in a type carrier @tc@.
-- The result maps every name to a pair @(fid,typ)@ of function id and C type specification.
-- The String list @tdn@ contains typedef names where to stop resolving external typedef names.
--
-- Retrieve the types carried by @tc@, get all derived part types, add fully resolved forms
-- (without stopping at @tdn@), convert function types to function pointer types,
-- omit all pointer to struct or union types (because they do not use a separate name) and all named function
-- pointer types (why?), translate the types to Cogent, and retrieve their names.
genDerivedTypeNames :: [String] -> LCA.DeclEvent -> FTrav [Map String (String,LCA.Type)]
genDerivedTypeNames tdn tc = do
    sfn <- srcFileName tc
    liftM (map (\(gt,fid,t) -> singleton (getName gt) (fid,t))) $ 
        mapM (\(fid,t) -> do gt <- transType fid t; return (gt,fid,t)) $ 
        filter (\(_,t) -> not $ (isCompPointer t || isNamedFunPointer t)) $ 
        nub $ map (\(fid,t) -> (fid,wrapFunAsPointer t)) $ 
        concat $ map (\(fid,t) -> nub [(fid,t), (fid,resolveFully [] t)]) $
        concat $ map (uncurry getDerivedParts) $ carriedWithFunIds sfn tdn tc
    where getName (GenType (CS.TCon nam [] _) _) = nam

-- | Generate a type definition for a Cogent name @nam@ of a derived type.
-- Additionall argument is a pair @(fid,typ)@ of function id and C type specification.
genDerivedTypeDefs :: String -> (String,LCA.Type) -> FTrav [GenToplv]

-- Note: Pointer to named function types are suppressed in genDerivedTypeNames
-- Derived type which contains typedef names:
-- Generate definition of the form
-- > type nam = resnam
-- where @resnam@ denotes the translation of the fully resolved derived type.
-- Here resolving does not stop at defined external typedef names, since we want to eliminate 
-- typedef names completely.
genDerivedTypeDefs nam (fid,t) | containsTypedefs t = do
    t <- transType fid $ resolveFully [] t
    return $ [GenToplv (CS.TypeDec nam [] t) noOrigin]
-- Pointer to void:
-- Generate abstract type definition.
genDerivedTypeDefs "P_Void" (_,_) = 
    return $ [GenToplv (CS.AbsTypeDec "P_Void" [] []) noOrigin]
-- Pointer to array type containing no typedef names:
-- @nam@ has the form @PA<size>El@. Generate definition of the form
-- > type PA<size>El = { cont: #A<size>El }
genDerivedTypeDefs nam (fid,(LCA.PtrType atyp@(LCA.ArrayType etyp as _ _) _ _)) = do
    t <- transType fid atyp
    let rectype = genType $ CS.TRecord [(pfieldnam, ((GenType (CS.TUnbox t) noOrigin), False))] markBox
    return $ [GenToplv (CS.TypeDec nam [] rectype) noOrigin]
    where pfieldnam = "cont"
-- Pointer to function type containing no typedef names:
-- @nam@ has the form @F_ARGS_RES@. Generate abstract definition.
genDerivedTypeDefs nam (fid,(LCA.PtrType ftyp@(LCA.FunctionType _ _) _ _)) = do
    return $ [GenToplv (CS.AbsTypeDec nam [] []) noOrigin]
-- Pointer to other type containing no typedef names:
-- @nam@ has the form @PRef@. Generate definition of the form
-- > type PRef = { cont: Ref }
genDerivedTypeDefs nam (fid,(LCA.PtrType t _ _)) | not $ (isFunction t || nam == "P_VOID") = do
    t <- transType "" t
    let rectype = genType $ CS.TRecord [(pfieldnam, (t, False))] markBox
    return $ [GenToplv (CS.TypeDec nam [] rectype) noOrigin]
    where pfieldnam = "cont"
-- Note: Pointer to composite types are suppressed in genDerivedTypeNames
-- Array type containing no typedef names:
-- @nam@ has the form @A<size>El@. Generate definitions of the form
-- > type UA<size>El
-- > type A<size>El = { arr: #UA<size>El }
genDerivedTypeDefs nam (fid,atyp@(LCA.ArrayType etyp as _ _)) = do
    return $ [tdef ("U"++nam),GenToplv (CS.TypeDec nam [] rectype) noOrigin]
    where pfieldnam = "arr"
          tdef nam = GenToplv (CS.AbsTypeDec nam [] []) noOrigin
          rectype = genType $ CS.TRecord [(pfieldnam, (genType (CS.TCon ("U"++nam) [] markUnbox), False))]  markBox
-- Note: function types are converted to function pointer type by genDerivedTypeNames

parmodFunId :: (LCA.Declaration d, LCN.CNode d) => d -> FTrav String
parmodFunId fdef = do
    sfn <- srcFileName $ LCA.declIdent fdef
    return $ getFunId fdef sfn

applyParmods :: LCA.Type -> String -> GenType -> FTrav GenType
applyParmods (LCA.FunctionType (LCA.FunType _ pars variadic) _) fid (GenType (CS.TFun pt rt) o) = do
    pms <- getParmods fid
    let vpms = if variadic then pms ++ ["no"] else pms
    dpms <- mapM mkDefaultParmod $ map LCA.declType pars
    let vdpms = if variadic then dpms ++ ["no"] else dpms
    let hpms = if (length vpms) < (length ptl) then vdpms else vpms
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
transMember sueref mdecl@(LCA.MemberDecl (LCA.VarDecl (LCA.VarName idnam _) att typ) _ n) | isArray typ = do
    t <- transType (getFunMemberId sueref mdecl) $ resolveTypedef typ
    let (GenType (CS.TCon nam [] b) _) = t
    return (mapIfUpper idnam, ((GenType (CS.TCon nam [] markUnbox) $ mkOrigin n), False))
transMember sueref mdecl@(LCA.MemberDecl (LCA.VarDecl (LCA.VarName idnam _) att typ) _ n) = do
    t <- transType (getFunMemberId sueref mdecl) typ
    return (mapIfUpper idnam, ((GenType (typeOfGT t) $ mkOrigin n), False))
{- LCA.AnonBitField cannot occur since it is always replaced by aggBitfields -}

transExtMember :: [String] -> LCI.SUERef -> LCA.MemberDecl -> FTrav (CCS.FieldName, (GenType, CS.Taken))
transExtMember tds sueref mdecl@(LCA.MemberDecl (LCA.VarDecl (LCA.VarName idnam _) att typ) _ n) = do
    t <- transType (getFunMemberId sueref mdecl) (resolveFully tds typ)
    return (mapIfUpper idnam, ((GenType (typeOfGT t) $ mkOrigin n), False))

transParamNames :: Bool -> [LCA.ParamDecl] -> FTrav GenIrrefPatn
transParamNames variadic [] = 
    return $ if variadic then variadicParamName else GenIrrefPatn CS.PUnitel noOrigin
transParamNames variadic [pd] = do
    pn <- transParamName pd
    return $ if variadic then GenIrrefPatn (CS.PTuple [pn, variadicParamName]) noOrigin else pn
transParamNames variadic pars = do
    ps <- mapM transParamName pars
    let vps = if variadic then ps ++ [variadicParamName] else ps
    return $ GenIrrefPatn (CS.PTuple vps) noOrigin

variadicParamName = GenIrrefPatn (CS.PVar "variadicCogentParameters") noOrigin

transParamName :: LCA.ParamDecl -> FTrav GenIrrefPatn
transParamName pd = 
    return $ GenIrrefPatn (CS.PVar $ mapIfUpper $ LCA.declIdent pd) $ noComOrigin pd

-- | Translate a C type specification to a Cogent type.
-- The first parameter is the function identifier to be used to retrieve a parmod description for 
-- a contained derived function type, or "" if no parmod description shall be used.
transType :: String -> LCA.Type -> FTrav GenType 

-- Type void:
-- Translate to: ()
transType _ (LCA.DirectType TyVoid _ _) = 
    return $ genType CS.TUnit
-- Complete function type: ret (p1,..,pn)
-- Translate to: Cogent function type (p1,..,pn) -> ret
transType fid (LCA.FunctionType (LCA.FunType ret pars variadic) _) = do
    r <- transType "" ret
    ps <- transParamTypes variadic fid pars
    return $ genType $ CS.TFun ps r
-- Other: direct type, typedef name, or derived type
-- Translate to: Cogent type name, possibly unboxed.
transType fid t = do
    (u,d,b) <- transDerivedType fid t
    return $ genType $ CS.TCon (mkDerivedName d b) [] $
        if u || isFunPointer t then markUnbox
                               else markBox

-- | Translate a C direct or derived type to a Cogent type name.
-- For first parameter see transType.
-- The result is a triple (u,d,b) where
--   u is whether the unbox operator must be applied,
--   d is the encoding of all derivation steps
--   b String is the name for the base type
transDerivedType :: String -> LCA.Type -> FTrav (Bool,String,String)

-- Type void (as base of a derived type):
-- Translate to: Void
transDerivedType _ (LCA.DirectType LCA.TyVoid _ _) = 
    return (False,"","Void")
-- Direct type:
-- Translate to primitive type name, Struct_... or Enum_...
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
-- Derived pointer type for type t:
-- Translate t. If unboxed make boxed, otherwise prepend P step. Always boxed.
transDerivedType fid (LCA.PtrType t quals _) = do
    (u,d,b) <- transDerivedType fid t
    if u then return (False,d,b)
         else return (False,mapPtrDeriv ++ d,b)
-- Derived array type for element type t:
-- Translate t. If struct or union type prepend U step. Then prepend A step. Always boxed.
transDerivedType fid (LCA.ArrayType t as quals _) = do
    (u,d,b) <- transDerivedType fid t
    return (False,(mapArrDeriv as) ++ (if isComposite t then mkNonLin d else d),b)
-- Derived complete function type for parameter types pars and result type rt:
-- Translate rt. If struct or union type prepend U step.
-- Adjust pars, translate, apply parmods. Prepend F step. Always unboxed.
-- Note parmods are not applied to result type in function pointer type names!
transDerivedType fid (LCA.FunctionType ft@(FunType rt pars variadic) _) = do
    (u,d,b) <- transDerivedType "" rt
    pts <- mapM (transDerivedType "") $ map adjustParamType parTypes
    defaultParmods <- mapM mkDefaultParmod parTypes
    pts <- applyParmodsDerived defaultParmods fid pts
    let vpts = if variadic then pts ++ [(False,mapParmodDeriv "no",variadicTypeName)] else pts
    return (True,(mapFunDeriv ft vpts) ++ (if isComposite rt then mkNonLin d else d),b)
    where parTypes = map LCA.declType pars
-- Derived incomplete function type for result type rt:
-- Translate rt. If struct or union type prepend U step. Then prepend F step. Always unboxed.
transDerivedType fid (LCA.FunctionType ft@(FunTypeIncomplete rt) _) = do
    (u,d,b) <- transDerivedType "" rt
    return (True,(mapFunDeriv ft []) ++ (if isComposite rt then mkNonLin d else d),b)
-- Typedef name:
-- Translate to mapped name. Unboxed for struct, union, or function, otherwise boxed.
transDerivedType _ (LCA.TypeDefType (LCA.TypeDefRef idnam typ _) quals _) =
    return (isCompOrFunc typ,"",tn)
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

mkBoxedType :: String -> Origin -> GenType
mkBoxedType nam = GenType (CS.TCon nam [] $ markBox)

mkUnboxedType :: String -> Origin -> GenType
mkUnboxedType nam = GenType (CS.TCon nam [] $ markUnbox)

mkFunType :: GenType -> GenType
mkFunType t@(GenType (CS.TFun _ _) _) = t
mkFunType t = genType $ CS.TFun (mkGenType []) t

-- The second argument is the parmod function identifier of the parameters' function.
transParamTypes :: Bool -> String -> [LCA.ParamDecl] -> FTrav GenType
transParamTypes variadic fid pars = do
    ps <- mapM (transParamType fid) pars
    return $ mkGenType (ps ++ if variadic then [variadicType] else [])

variadicType = genType (CS.TCon variadicTypeName [] markBox)
variadicTypeName = "VariadicCogentParameters"

transParamType :: String -> LCA.ParamDecl -> FTrav GenType
transParamType fid pd = do
    t <- transType (getLocalFunId fid pd) $ adjustParamType ptyp
    return $ GenType (typeOfGT t) $ origin pd
    where (LCA.VarDecl _ _ ptyp) = getVarDecl pd

adjustParamType :: LCA.Type -> LCA.Type
--adjustParamType t | isArray t = (LCA.PtrType elt quals attrs)
--    where (LCA.ArrayType elt _ quals attrs) = resolveTypedef t
adjustParamType t | isFunction t = (LCA.PtrType t LCA.noTypeQuals LCA.noAttributes)
adjustParamType t = t

arraySizeType :: LCA.ArraySize -> GenType
arraySizeType (LCA.ArraySize _ (LCS.CConst (LCS.CIntConst ci _))) =
    genType $ CS.TCon tnam [] markBox
    where tnam = if i < 257 then "U8" else if i < 65537 then "U16" else "U32"
          i = LC.getCInteger ci
arraySizeType _ = genType $ CS.TCon "U32" [] markBox

dummyExpr :: LCA.Type -> FTrav RawExpr
dummyExpr (LCA.DirectType TyVoid _ _) = 
    return $ CS.RE CS.Unitel
dummyExpr (LCA.DirectType (LCA.TyComp _) _ _) = do
    return $ dummyApp "gencotDummy"
dummyExpr (LCA.DirectType _ _ _) = do
    return $ CS.RE $ CS.IntLit 0
dummyExpr (LCA.TypeDefType (LCA.TypeDefRef idnam typ _) _ _) = return $
    case rtyp of
         (LCA.DirectType (LCA.TyComp _) _ _) -> dummyApp "gencotDummy"
         (LCA.DirectType TyVoid _ _) -> CS.RE CS.Unitel
         (LCA.DirectType _ _ _) -> CS.RE $ CS.IntLit 0
         _ -> dummyApp "gencotDummy"
    where rtyp = resolveTypedef typ
dummyExpr _ = do
    return $ dummyApp "gencotDummy"

dummyAppExpr :: CS.RawExpr -> CS.RawExpr
dummyAppExpr fun = CS.RE $ CS.App fun (CS.RE CS.Unitel) False

dummyApp :: String -> CS.RawExpr
dummyApp fnam = dummyAppExpr $ CS.RE $ CS.Var fnam

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

