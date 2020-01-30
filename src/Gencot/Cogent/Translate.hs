{-# LANGUAGE PackageImports #-}
module Gencot.Cogent.Translate where

import Control.Monad (liftM,when)
import Data.List (nub,isPrefixOf)
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

import Gencot.Origin (Origin,noOrigin,origin,mkOrigin,noComOrigin,mkBegOrigin,mkEndOrigin,prepOrigin,appdOrigin,isNested,toNoComOrigin)
import Gencot.Names (transTagName,transObjName,mapIfUpper,mapNameToUpper,mapNameToLower,mapPtrDeriv,mapPtrVoid,mapMayNull,mapArrDeriv,mapFunDeriv,arrDerivHasSize,arrDerivToUbox,mapUboxStep,rmUboxStep,mapMayNullStep,rmMayNullStep,mapPtrStep,mapFunStep,mapIncFunStep,mapArrStep,mapModStep,mapRoStep,mapNamFunStep,srcFileName)
import Gencot.Cogent.Ast
import Gencot.C.Translate (transStat,transExpr)
import Gencot.Traversal (FTrav,getParmods,markTagAsNested,isMarkedAsNested,isSafePointer)
import Gencot.Util.Types (carriedTypes,getDerivedParts,usedTypeNames,resolveFully,isExtern,isCompOrFunc,isCompPointer,isNamedFunPointer,isFunPointer,isPointer,isAggregate,isFunction,isTypeDefRef,isComplete,isArray,isVoid,isTagRef,containsTypedefs,resolveTypedef,isComposite,isLinearType,isLinearParType,isReadOnlyType,isReadOnlyParType,wrapFunAsPointer,getTagDef)
import Gencot.Json.Identifier (getFunId,getFunMemberId,getFunTypeId,getLocalFunId,carriedWithFunIds)

genType t = GenType t noOrigin

-- | Translate a sequence of C "external" (global) declarations to a sequence of Cogent toplevel definitions.
transGlobals :: [LCA.DeclEvent] -> FTrav [GenToplv]
transGlobals tcs = liftM concat $ mapM transGlobal tcs

-- | Translate a C "external" (global) declaration to a sequence of Cogent toplevel definitions.
-- A single C declaration with nested declarations may be translated to a sequence of Cogent definitions.
transGlobal :: LCA.DeclEvent -> FTrav [GenToplv]
-- Translate a C struct definition -> see transStruct
transGlobal (LCA.TagEvent (LCA.CompDef ct@(LCA.CompType _ LCA.StructTag _ _ _))) =
    transStruct ct transMember
-- If not yet translated as nested, translate a C union definition of the form
-- > union tagname { ... }
-- to an abstract Cogent type definition of the form
-- > type Union_tagname
-- (if tagname is not present use a synthetic tagname constructed from the source position).
transGlobal (LCA.TagEvent (LCA.CompDef (LCA.CompType sueref LCA.UnionTag _ _ n))) = do
    nst <- isMarkedAsNested sueref
    if nst 
       then return []
       else do
           tn <- transTagName $ LCA.TyComp $ LCA.CompTypeRef sueref LCA.UnionTag n
           return $ [GenToplv (CS.AbsTypeDec tn [] []) $ mkOrigin n]
-- If not yet translated as nested, translate a C enum definition of the form
-- > enum tagname { ... }
-- to a Cogent type definition of the form
-- > type Enum_tagname = U32
-- (only if the tagname is present).
transGlobal (LCA.TagEvent (LCA.EnumDef (LCA.EnumType sueref es _ n))) = do
    nst <- isMarkedAsNested sueref
    if nst || LCI.isAnonymousRef sueref
       then return []
       else do
           tn <- transTagName $ LCA.TyEnum $ LCA.EnumTypeRef sueref n
           return $ [GenToplv (CS.TypeDec tn [] $ genType $ CS.TCon "U32" [] markUnbox) $ mkOrigin n]
-- Translate an object or complete function declaration of the form
-- > typ name;
-- (where type may be a derived type syntactically integrated in the name)
-- to a Cogent abstract function definition of the form
-- > name :: funtyp
-- If the C object is not a function, the Cogent function is a parameterless
-- access function of type () -> typ
transGlobal (LCA.DeclEvent (LCA.Declaration decl@(LCA.Decl _ n))) | isComplete typ = do
    f <- transObjName $ LCA.declIdent decl
    fid <- parmodFunId decl
    t <- transType False fid typ
    nt <- transTagIfNested typ n
    return $ wrapOrigin n (nt ++ [GenToplv (CS.AbsDec f (CS.PT [] $ mkFunType t)) noOrigin])
    where typ = LCA.declType decl
-- Translate a C function definition of the form
-- > rt name(parlist) { stmt }
-- to a Cogent function definition of the form
-- > name :: (partypes) -> rt
-- > name (parnames) = dummy {- stmt -}
-- where @partypes@, @rt@, and @dummy@ are modified according to a parameter modification description
-- and stmt is translated by mapping all non-local names.
transGlobal (LCA.DeclEvent (LCA.FunctionDef fdef@(LCA.FunDef decl stat n))) = do
    f <- transObjName $ LCA.declIdent decl
    fid <- parmodFunId fdef
    t <- transType False fid typ
    nt <- transTagIfNested typ n -- wirkt erst wenn transTagIfNested auch derived types verarbeitet
    ps <- transParamNames isVar pars
    LCA.enterFunctionScope
    LCA.defineParams LCN.undefNode decl
    d <- dummyExpr res
    d <- extendExpr fdef d pars
    s <- transStat stat
    LCA.leaveFunctionScope
    return $ wrapOrigin n (nt ++ [GenToplv (CS.FunDef f (CS.PT [] t) [CS.Alt ps CCS.Regular $ FunBody d s]) noOrigin])
    where typ = LCA.declType decl
          (LCA.FunctionType (LCA.FunType res pars isVar) _) = typ
-- Translate a C object definition of the form
-- > typ name = expr;
-- (where type may be a derived type syntactically integrated in the name)
-- to a Cogent abstract function definition of the form
-- > name :: () -> typ
-- for a parameterless access function
transGlobal (LCA.DeclEvent odef@(LCA.ObjectDef (LCA.ObjDef decl@(LCA.VarDecl (LCA.VarName idnam _) _ typ) _ n))) = do
    f <- transObjName idnam
    fid <- parmodFunId odef
    t <- transType False fid typ
    nt <- transTagIfNested typ n
    return $ wrapOrigin n (nt ++ [GenToplv (CS.AbsDec f (CS.PT [] $ mkFunType t)) noOrigin])
-- Translate a C enumerator definition of the form
-- > name = expr;
-- to a Cogent constant definition of the form
-- > name :: U32
-- > name = expr
-- where @expr@ is the orginal C expression with mapped names.
transGlobal (LCA.DeclEvent (LCA.EnumeratorDef (LCA.Enumerator idnam expr _ n))) = do
    e <- transExpr expr
    return $ [GenToplv (CS.ConstDef en (genType $ CS.TCon "U32" [] markUnbox) $ ConstExpr e) $ mkOrigin n]
    where en = mapNameToLower idnam
-- Translate a typedef of the form
-- > typedef type-specifier declarator;
-- where @declarator@ denotes a (derived type for an) identifier @idnam@.
-- If the @type-specifier@ denotes a struct or union type the typedef is first adjusted
-- by replacing @idnam@ by @*idnam@, i.e. the typedef name is defined for a pointer to
-- struct, or union type. Array types need no adjusting, they are always adjusted by @transType@.
-- The translation result has the form
-- > type idnam = type
-- where @type@ is constructed by translating @type-specifier@ and applying all derivations from the adjusted @declarator@.
-- A MayNull application to type is removed.
transGlobal (LCA.TypeDefEvent td@(LCA.TypeDef idnam typ _ n)) = do
    t <- transType False (getFunTypeId td) modiftyp
    nt <- transTagIfNested typ n
    return $ wrapOrigin n (nt ++ [GenToplv (CS.TypeDec tn [] (rmMayNull t)) noOrigin])
    where tn = mapNameToUpper idnam
          modiftyp = if isComposite typ then (LCA.PtrType typ LCA.noTypeQuals [])
                                        else typ
transGlobal _ = return $ [GenToplv (CS.Include "err-unexpected toplevel") noOrigin]

transExtGlobals :: [String] -> [LCA.DeclEvent] -> FTrav [GenToplv]
transExtGlobals tds tcs = liftM concat $ mapM (transExtGlobal tds) tcs

transExtGlobal :: [String] -> LCA.DeclEvent -> FTrav [GenToplv]
transExtGlobal tds (LCA.TypeDefEvent td@(LCA.TypeDef idnam typ _ n)) = do
    t <- transType False (getFunTypeId td) restyp
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

-- | If not yet translated as nested, translate a C struct definition of the form
-- > struct tagname { ... }
-- to a Cogent record definition of the form
-- > type Struct_tagname = { ... }
-- The second parameter is a monadic action which translates a single member declaration
-- to a pair of Cogent field name and type. As additional first parameter it expects the reference
-- to the C struct type definition.
-- All nested tag definitions are translated and appended as separate toplevel type definitions.
transStruct :: LCA.CompType -> (LCI.SUERef -> LCA.MemberDecl -> FTrav (CCS.FieldName, (GenType, CS.Taken))) -> FTrav [GenToplv]
transStruct (LCA.CompType sueref LCA.StructTag mems _ n) trMember = do
    nst <- isMarkedAsNested sueref
    if nst 
       then return []
       else do
           tn <- transTagName $ LCA.TyComp $ LCA.CompTypeRef sueref LCA.StructTag n
           ms <- mapM (trMember sueref) aggmems
           nts <- liftM concat $ mapM transMemTagIfNested aggmems
           return $ wrapOrigin n ([GenToplv (CS.TypeDec tn [] $ genType $ CS.TRecord ms markBox) noOrigin] ++ nts)
    where utyp = genType CS.TUnit
          aggmems = aggBitfields mems

-- | Translate nested tag definitions in a member definition.
transMemTagIfNested :: LCA.MemberDecl -> FTrav [GenToplv]
transMemTagIfNested mdecl = transTagIfNested (LCA.declType mdecl) $ LCN.nodeInfo mdecl

-- | Translate a C type as nested tag definition.
-- Additional second parameter is the position where the type is used.
-- If the type is a reference to a struct,union, or enum, lookup its definition.
-- If the definition is at the same position where the type is used, then
-- it is nested at that position. Translate it and mark it as nested in the user state.
transTagIfNested :: LCA.Type -> LCN.NodeInfo -> FTrav [GenToplv]
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

-- | Generate type definitions for all derived array and function pointer types used by a sequence of C declarations.
-- The String list @tdn@ contains typedef names where to stop resolving external typedef names.
genTypeDefs :: [String] -> [LCA.DeclEvent] -> FTrav [GenToplv]
genTypeDefs tdn tcs = do
    derivedTypes <- liftM (unions . concat) $ mapM (genDerivedTypeNames tdn) tcs
    (liftM concat) $ mapM (uncurry genDerivedTypeDefs) $ toList derivedTypes

-- | Construct all names of derived array and function pointer types occurring in a type carrier @tc@.
-- The result is a map from names of generic types used for mapped array types and names of
-- abstract types used for function pointer types to pairs consisting of a function id and the 
-- original C array or function pointer type.
-- The String list @tdn@ contains typedef names where to stop resolving external typedef names.
--
-- Retrieve the types carried by @tc@, get all derived part types,
-- add fully resolved forms (without stopping at @tdn@), 
-- convert function types to function pointer types (because all function types here occur at places where they are adjusted),
-- reduce to derived array and function pointer types, 
-- omit all named function pointer types (because they do not contain the function type argument), 
-- translate the types to Cogent, and retrieve their names.
genDerivedTypeNames :: [String] -> LCA.DeclEvent -> FTrav [Map String (String,LCA.Type)]
genDerivedTypeNames tdn tc = do
    sfn <- srcFileName tc
    liftM (map (\(gt,fid,t) -> singleton (getName gt) (fid,t))) $ 
        mapM (\(fid,t) -> do gt <- transType False fid t; return (gt,fid,t)) $ 
        filter (\(_,t) -> isArray t || (isFunPointer t && (not $ isTypeDefRef t))) $
        nub $ map (\(fid,t) -> (fid,wrapFunAsPointer t)) $ 
        concat $ map (\(fid,t) -> nub [(fid,t), (fid,resolveFully [] t)]) $
        concat $ map (uncurry getDerivedParts) $ carriedWithFunIds sfn tdn tc
    where --getName (GenType (CS.TCon nam [t] _) _) =
            --if nam == (mapFunDeriv False) || nam == (mapFunDeriv True) then argName t else nam
          --argName (GenType (CS.TCon nam _ _) _) = nam
          getName (GenType (CS.TCon nam _ _) _) = nam

-- | Generate type definitions for a Cogent type name @nam@ used by a derived array or function pointer type.
-- Additional argument is a pair @(fid,typ)@ of function id and C type specification.
genDerivedTypeDefs :: String -> (String,LCA.Type) -> FTrav [GenToplv]
-- For a derived array type the name has the form @CArr<size>@, @CArrX<size>X@ or @CArrXX@.
-- The last case is ignored.
-- For the other cases two generic type defintions are generated of the form
-- > type CArr... el = { arr: #(UArr... el) }
-- > type UArr... el
genDerivedTypeDefs nam (fid,(LCA.ArrayType _ _ _ _)) | arrDerivHasSize nam =
    return [tdef nam,adef $ arrDerivToUbox nam]
    where tdef nam = GenToplv (CS.TypeDec nam ["el"] $ genType $ CS.TRecord [("arr", (ftyp nam, False))] markBox) noOrigin
          ftyp nam = genType $ CS.TCon (arrDerivToUbox nam) [genType $ CS.TVar "el" False False] markUnbox
          adef nam = GenToplv (CS.AbsTypeDec nam ["el"] []) noOrigin
-- For a derived function pointer type the name has the form @CFunPtr_enc@ or @CFunInc_enc@ where
-- @enc@ is an encoded C type. First we determine the corresponding type where all typedef names are resolved.
-- If that is different from @nam@ then @nam@ contains typedef names. In that case generate a type synonym definition
-- > type nam = resnam
-- where resnam is the name with all typedef names resolved. Otherwise generate an abstract type definition of the form
-- > type nam
-- In the case of a complete function type additionally introduce a synonym for the corresponding
-- function type of the form
-- > type CFun_enc = <Cogent mapping of C function type>
genDerivedTypeDefs nam (fid,pt@(LCA.PtrType t _ _)) = do
    rslvtyp <- transType True fid pt
    let tdef = if getName rslvtyp == nam
                then CS.AbsTypeDec nam [] []
                else CS.TypeDec nam [] rslvtyp
    typ <- transType False fid t
    let fdef = GenToplv (CS.TypeDec fnam [] typ ) noOrigin
    return $ (GenToplv tdef noOrigin): if (mapFunDeriv True) `isPrefixOf` nam then [fdef] else []
    where fnam = "CFun" ++ (drop (length (mapFunDeriv True)) nam)
          getName (GenType (CS.TCon nam _ _) _) = nam
genDerivedTypeDefs _ _ = return []

parmodFunId :: (LCA.Declaration d, LCN.CNode d) => d -> FTrav String
parmodFunId fdef = do
    sfn <- srcFileName $ LCA.declIdent fdef
    return $ getFunId fdef sfn

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
          procBitfield :: LCS.CExpr -> [LCA.MemberDecl] -> LCN.NodeInfo -> [LCA.MemberDecl]
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
          bitfieldgrp :: CExpr -> [LCA.MemberDecl] -> LCN.NodeInfo -> LCA.MemberDecl
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

-- | Translate struct member definition to pair of Cogent record field name and type.
-- First parameter is the reference to the enclosing struct type, it is used to construct a function id for the member.
transMember :: LCI.SUERef -> LCA.MemberDecl -> FTrav (CCS.FieldName, (GenType, CS.Taken))
transMember sueref mdecl@(LCA.MemberDecl (LCA.VarDecl (LCA.VarName idnam _) _ typ) _ n) =
    transMemberDef (getFunMemberId sueref mdecl) idnam typ n
{- LCA.AnonBitField cannot occur since it is always replaced by aggBitfields -}

-- | Translate external struct member definition to pair of Cogent record field name and type.
-- The member type is fully resolved.
-- The additional first parameter is a list of type names where to stop resolving.
transExtMember :: [String] -> LCI.SUERef -> LCA.MemberDecl -> FTrav (CCS.FieldName, (GenType, CS.Taken))
transExtMember tds sueref mdecl@(LCA.MemberDecl (LCA.VarDecl (LCA.VarName idnam _) _ typ) _ n) = 
    transMemberDef (getFunMemberId sueref mdecl) idnam (resolveFully tds typ) n

-- | Translate struct member definition to pair of Cogent record field name and type.
-- Translate member type, if array set unboxed. Map member name if it starts with uppercase.
transMemberDef :: String -> LCI.Ident -> LCA.Type -> LCN.NodeInfo -> FTrav (CCS.FieldName, (GenType, CS.Taken))
transMemberDef fid idnam typ n = do
    t <- transType False fid typ
    let ut = if isArray typ then setUnboxed t else t
    return (mapIfUpper idnam, (setOrigin n ut, False))

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
-- The first parameter specifies whether typedef names shall be resolved.
-- The second parameter is the function identifier to be used to retrieve a parmod description for 
-- a contained derived function type, or "" if no parmod description shall be used.
transType :: Bool -> String -> LCA.Type -> FTrav GenType 

-- Type void:
-- Translate to: ()
transType _ _ (LCA.DirectType LCA.TyVoid _ _) = 
    return $ genType CS.TUnit
-- Direct type:
-- Translate to: Name of primitive type (boxed) or composite type (unboxed).
-- Remark: Semantically, primitive types are unboxed. 
-- However, if marked as unboxed the Cogent prettyprinter adds a (redundant) unbox operator.
transType _ _ (LCA.DirectType tnam _ _) = do
    tn <- transTNam tnam
    return $ genType $ CS.TCon tn [] ub 
    where ub = case tnam of
                (LCA.TyComp _) -> markUnbox
                _ -> markBox
-- Typedef name:
-- If resolving, translate the referenced type.
-- Otherwise translate to mapped name. Unboxed for struct, union, function, or function pointer, otherwise boxed.
-- If the typedef name is a safe pointer, omit or remove MayNull
-- otherwise move a MayNull from the resolved type to the mapped name.
transType rslv fid (LCA.TypeDefType (LCA.TypeDefRef idnam typ _) _ _) = do
    safe <- isSafePointer ("typedef|" ++ (identToString idnam))
    rslvtyp <- transType True fid typ
    if rslv
       then return $ rmMayNullIf safe rslvtyp
       else return $ addMayNullIfNot (safe || (not $ hasMayNull rslvtyp)) rtyp
    where tn = mapNameToUpper idnam
          ub = if (isCompOrFunc typ) || (isFunPointer typ) then markUnbox else markBox
          rtyp = genType $ CS.TCon tn [] ub
-- Pointer to void:
-- Translate to: CVoidPtr
-- If not safe pointer: MayNull CVoidPtr
transType _ fid (LCA.PtrType t _ _) | isVoid t = do
    safe <- isSafePointerType fid t 
    return $ addMayNullIfNot safe $ genType $ CS.TCon mapPtrVoid [] markBox
-- Derived pointer type for unnamed function type t:
-- Encode t, apply CFunPtr or CFunInc and make unboxed.
transType rslv fid (LCA.PtrType t _ _) | isFunction t = do
    enctyp <- encodeType rslv fid t
    return $ genType $ CS.TCon ((mapFunDeriv $ isComplete t) ++ "_" ++ enctyp) [] markUnbox
-- Derived pointer type for array type t:
-- Translate t and use as result. Always boxed.
-- If not safe pointer: apply MayNull
transType rslv fid (LCA.PtrType t _ _) | isArray t = do
    safe <- isSafePointerType fid t
    typ <- transType rslv "" t
    return $ addMayNullIfNot safe typ
-- Derived pointer type for other type t:
-- Translate t. If unboxed and no function pointer make boxed, otherwise apply CPtr. Always boxed.
-- If not safe pointer apply MayNull.
transType rslv fid (LCA.PtrType t _ _) = do
    safe <- isSafePointerType fid t 
    typ <- transType rslv "" t
    let rtyp = if (isUnboxed typ) && not (isFunPointer t) 
                then setBoxed typ
                else genType $ CS.TCon mapPtrDeriv [typ] markBox
    return $ addMayNullIfNot safe rtyp
-- Complete derived function type: ret (p1,..,pn)
-- Translate to: Cogent function type (p1,..,pn) -> ret, then apply parmod description.
-- If @fid@ is in safe pointer list remove MayNull from result type if present.
transType rslv fid t@(LCA.FunctionType (LCA.FunType ret pars variadic) _) = do
    safe <- isSafePointer fid
    r <- transType rslv "" ret
    ps <- transParamTypes variadic rslv fid pars
    applyParmods t fid $ genType $ CS.TFun ps $ rmMayNullIf safe r
-- Derived array type for array type t (multidimensional array):
-- Translate t, apply unbox operator, then apply generic array type. Always boxed.
transType rslv _ (LCA.ArrayType t as _ _) | isArray t = do
    typ <- transType rslv "" t
    return $ genType $ CS.TCon (mapArrDeriv as) [setUnboxed typ] markBox 
-- Derived array type for non-array type t:
-- Translate t using function id only if pointer type, apply generic array type. Always boxed.
transType rslv fid (LCA.ArrayType t as _ _) = do
    typ <- transType rslv usefid t
    return $ genType $ CS.TCon (mapArrDeriv as) [typ] markBox 
    where usefid = if isPointer t then fid else ""

-- | Encode a C type specification as a Cogent type name.
-- The first parameter specifies whether typedef names shall be resolved.
-- The second parameter is the function identifier to be used to retrieve a parmod description for 
-- a contained derived function type, or "" if no parmod description shall be used.
encodeType :: Bool -> String -> LCA.Type -> FTrav String
-- Type void:
-- Encode as: Void
encodeType _ _ (LCA.DirectType LCA.TyVoid _ _) = 
    return "Void"
-- Direct type:
-- Encode as: Name of primitive type or composite type.
-- For composite type prepend unbox step.
encodeType _ _ (LCA.DirectType tnam _ _) = do
    tn <- transTNam tnam
    return (ustep ++ tn)
    where ustep = case tnam of
                (LCA.TyComp _) -> mapUboxStep
                _ -> ""
-- Typedef name:
-- If resolving, encode the referenced type.
-- Otherwise, encode as mapped name. For struct, union, or array prepend unbox step.
-- If the typedef name is a safe pointer, omit or remove MayNull step
-- otherwise move a MayNull step from the resolved type to the mapped name.
encodeType rslv fid (LCA.TypeDefType (LCA.TypeDefRef idnam typ _) _ _) = do
    safe <- isSafePointer ("typedef|" ++ (identToString idnam))
    rslvtyp <- encodeType True fid typ
    if rslv
       then return $ rmMayNullStepIf safe rslvtyp
       else return $ addMayNullStepIfNot (safe || (not $ hasMayNullStep rslvtyp)) rtyp
    where tn = mapNameToUpper idnam
          ustep = if isAggregate typ then mapUboxStep else ""
          rtyp = (ustep ++ tn)
-- Derived pointer type for aggregate type t:
-- Encode t, for aggregate type remove unbox step, otherwise prepend pointer derivation step.
-- If not a safe pointer, add MayNull step.
encodeType rslv fid (LCA.PtrType t _ _) = do
    safe <- isSafePointerType fid t
    tn <- encodeType rslv "" t
    let htn = if isAggregate t then (rmUboxStep tn) else (mapPtrStep ++ tn)
    return $ addMayNullStepIfNot safe htn
-- Complete derived function type: ret (p1,..,pn)
-- Encode ret, prepend function derivation step using encoded pi.
-- If @fid@ is in safe pointer list remove MayNull step from result type if present.
encodeType rslv fid t@(LCA.FunctionType (LCA.FunType ret pars variadic) _) = do
    safe <- isSafePointer fid
    tn <- encodeType rslv "" ret
    ps <- encodeParamTypes variadic rslv fid pars
    return ((mapFunStep ps) ++ (rmMayNullStepIf safe tn))
-- Incomplete derived function type: ret ()
-- Encode ret, prepend incomplete function derivation step.
-- If @fid@ is in safe pointer list remove MayNull step from result type if present.
encodeType rslv fid t@(LCA.FunctionType (LCA.FunTypeIncomplete ret) _) = do
    safe <- isSafePointer fid
    tn <- encodeType rslv "" ret
    return (mapIncFunStep ++ (rmMayNullStepIf safe tn))
-- Derived array type for element type t:
-- Encode t using function id only if pointer type, prepend array derivation step and unbox step.
encodeType rslv fid (LCA.ArrayType t as _ _) = do
    tn <- encodeType rslv usefid t
    return (mapUboxStep ++ (mapArrStep as) ++ tn)
    where usefid = if isPointer t then fid else ""

-- | Translate a C type name to a Cogent type name.
transTNam :: LCA.TypeName -> FTrav String
transTNam tnam@(LCA.TyComp _) = transTagName tnam
transTNam (LCA.TyEnum (LCA.EnumTypeRef (AnonymousRef _) _)) = return "U32"
transTNam tnam@(LCA.TyEnum _) = transTagName tnam
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

isSafePointerType :: String -> LCA.Type -> FTrav Bool
isSafePointerType fid t = do
    safe1 <- isSafePointer fid 
    safe2 <- if null tag then return False else isSafePointer (tag ++ "*")
    safe3 <- if null tnam then return False else isSafePointer ("typedef|" ++ tnam ++ "*")
    return (safe1 || safe2 || safe3)
    where tag = getTag t
          tnam = getTypedefName t

rmMayNullIf :: Bool -> GenType -> GenType
rmMayNullIf s t = if s then rmMayNull t else t

addMayNullIfNot :: Bool -> GenType -> GenType
addMayNullIfNot s t =
    if s then t
         else genType $ CS.TCon mapMayNull [t] markBox

rmMayNullStepIf :: Bool -> String -> String
rmMayNullStepIf s t = if s then rmMayNullStep t else t
    
addMayNullStepIfNot :: Bool -> String -> String
addMayNullStepIfNot s t =
    if s then t
         else (mapMayNullStep ++ t)

rmMayNull :: GenType -> GenType
rmMayNull (GenType (CS.TCon tn [t] _) _) | tn == mapMayNull = t
rmMayNull t = t

hasMayNull :: GenType -> Bool
hasMayNull (GenType (CS.TCon tn _ _) _) | tn == mapMayNull = True
hasMayNull _ = False

hasMayNullStep :: String -> Bool
hasMayNullStep t = mapMayNullStep `isPrefixOf` t

getTag :: LCA.Type -> String
getTag (LCA.DirectType (LCA.TyComp (LCA.CompTypeRef sueref _ _)) _ _) = sueRefToString sueref
getTag (LCA.TypeDefType (LCA.TypeDefRef _ typ _) _ _) = getTag typ
getTag _ = ""

getTypedefName :: LCA.Type -> String
getTypedefName (LCA.TypeDefType (LCA.TypeDefRef nam _ _) _ _) = identToString nam
getTypedefName t = ""

-- | Apply parameter modification description to a mapped function type.
-- The first parameter is the original C function type.
-- The second parameter is the function id of the associated parameter modification description.
-- If the parameter modification description has fewer parameters than the function type,
-- apply the default parameter modification description instead.
applyParmods :: LCA.Type -> String -> GenType -> FTrav GenType
applyParmods (LCA.FunctionType (LCA.FunType _ pars variadic) _) fid (GenType (CS.TFun pt rt) o) = do
    pms <- getParamMods fid pars variadic
    let pts = zip pms ptl
    return $ GenType (CS.TFun (applyToPars pts) (applyToRes pts rt)) o
    where ptl = ptlist pt
          ptlist (GenType CS.TUnit _) = []
          ptlist (GenType (CS.TTuple ts) _) = ts
          ptlist gt = [gt]
applyParmods _ _ t = return t

-- | Prepare parameter modification specifications for a given parameter declaration list.
-- First parameter is the function identifier of the parameters' function.
-- Third parameter tells whether the function is variadic.
getParamMods :: String -> [LCA.ParamDecl] -> Bool -> FTrav [String]
getParamMods fid pars variadic = do
    pms <- getParmods fid
    let vpms = if variadic then pms ++ ["no"] else pms
    dpms <- mapM mkDefaultParmod pts
    let vdpms = if variadic then dpms ++ ["no"] else dpms
    if (length vpms) < (length vdpms) then return vdpms else return vpms
    where pts = map LCA.declType pars
    
-- | Apply parameter modification description to parameters of a mapped function type.
-- Input is a list of parameter types with associated modification description (as a String).
-- Output is the type for the parameter list (unit, singleton, or tuple).
applyToPars :: [(String,GenType)] -> GenType
applyToPars pts = mkGenType $ map applyToPar pts

-- | Apply parameter modification description to a single parameter type.
-- The description is a string.
-- If the C type is readonly or the parameter is not modified, the Cogent type is changed to readonly.
applyToPar :: (String,GenType) -> GenType
applyToPar (s,gt) | s == "readonly" || s == "no" = genType $ CS.TBang gt
applyToPar (_,gt) = gt

-- | Apply parameter modification to a function result type.
-- Additional input is a list of parameter types with associated modification description (as a String).
-- For every parameter which is modified, its type is appended to the result type.
-- Comment markers are removed from these types to avoid duplication of comments.
-- Output is the type for the result list (unit, singleton, or tuple).
applyToRes :: [(String,GenType)] -> GenType -> GenType
applyToRes pts rt = mkGenType $ addrps rt
    where rps = map remComment $ map snd $ filter (((==) "yes") . fst) pts
          addrps (GenType CS.TUnit _) = rps
          addrps t = t : rps

-- | Create default parameter modification description for a single C parameter type.
-- If the C type is not linear or readonly, specify this property.
-- Otherwise assume that it is modified.
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

-- | Translate a sequence of C parameter declarations to the corresponding Cogent parameter type.
-- The result is either the unit type, a single type, or a tuple type (for more than 1 parameter).
-- The first argument specifies whether the function is variadic, in this case a pseudo parameter is added.
-- The second argument specifies whether typedef names shall be resolved.
-- The third argument is the parmod function identifier of the parameters' function. It is used to 
-- construct the parmod function identifiers for parameters of function (pointer (array)) type.
transParamTypes :: Bool -> Bool -> String -> [LCA.ParamDecl] -> FTrav GenType
transParamTypes variadic rslv fid pars = do
    ps <- mapM (transParamType rslv fid) pars
    return $ mkGenType (ps ++ if variadic then [variadicType] else [])

variadicType = genType (CS.TCon variadicTypeName [] markBox)
variadicTypeName = "VariadicCogentParameters"

-- | Translate a C parameter declaration to the adjusted Cogent parameter type.
transParamType :: Bool -> String -> LCA.ParamDecl -> FTrav GenType
transParamType rslv fid pd = do
    t <- transType rslv (getLocalFunId fid pd) $ adjustParamType ptyp
    return $ GenType (typeOfGT t) $ origin pd
    where (LCA.VarDecl _ _ ptyp) = getVarDecl pd

-- | Adjust a C type used as parameter type.
-- Parameters of function type are adjusted to function pointer type.
-- Parameters of array type need not be adjusted because they are always translated as pointer to array.
adjustParamType :: LCA.Type -> LCA.Type
--adjustParamType t | isArray t = (LCA.PtrType elt quals attrs)
--    where (LCA.ArrayType elt _ quals attrs) = resolveTypedef t
adjustParamType t | isFunction t = (LCA.PtrType t LCA.noTypeQuals LCA.noAttributes)
adjustParamType t = t

-- | Encode the types of a parameter declaration list.
-- The first argument specifies whether the function is variadic.
-- The second argument specifies whether typedef names shall be resolved.
-- The third argument is the function identifier of the parameters' function.
-- Encode the parameter types, append variadic pseudo parameter, apply parameter modification descriptions.
encodeParamTypes :: Bool -> Bool -> String -> [LCA.ParamDecl] -> FTrav [String]
encodeParamTypes variadic rslv fid pars = do
    encpars <- mapM (encodeParamType rslv fid) pars
    pms <- getParamMods fid pars variadic
    let vencpars = if variadic then encpars ++ [variadicTypeName] else encpars
    return $ map applyEncodeParmod $ zip pms vencpars

-- | Encode a type as parameter type.
-- For an array type: adjust by removing unbox step.
encodeParamType :: Bool -> String -> LCA.ParamDecl -> FTrav String
encodeParamType rslv fid pd = do
    typ <- encodeType rslv (getLocalFunId fid pd) ptyp
    if isArray ptyp 
       then return $ rmUboxStep typ
       else return typ
    where ptyp = LCA.declType pd

-- | Apply parameter modification to an encoded parameter type.
-- For "yes" prepend modification pseudo step.
-- For "readonly" and "no" prepend readonly pseudo step.
-- For "nonlinear" and "discarded" do nothing.
applyEncodeParmod :: (String,String) -> String
applyEncodeParmod ("yes",s) = mapModStep ++ s
applyEncodeParmod ("readonly",s) = mapRoStep ++ s
applyEncodeParmod ("no",s) = mapRoStep ++ s
applyEncodeParmod (_,s) = s

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
setBoxed (GenType (CS.TRecord fields _) o) = (GenType (CS.TRecord fields markBox) o)
setBoxed (GenType (CS.TUnbox (GenType t _)) o) = (GenType t o)

setUnboxed :: GenType -> GenType
setUnboxed (GenType (CS.TCon nam p _) o) = (GenType (CS.TCon nam p markUnbox) o)
setUnboxed (GenType (CS.TRecord fields _) o) = (GenType (CS.TRecord fields markUnbox) o)
setUnboxed (GenType t o) = (GenType (CS.TUnbox (GenType t noOrigin)) o)

isUnboxed :: GenType -> Bool
isUnboxed (GenType (CS.TCon _ _ CCT.Unboxed) _) = True
isUnboxed (GenType (CS.TRecord _ CCT.Unboxed) _) = True
isUnboxed (GenType (CS.TUnbox _) _) = True
isUnboxed _ = False

markBox = CCT.Boxed False CS.noRepE
markUnbox = CCT.Unboxed

setOrigin :: LCN.NodeInfo -> GenType -> GenType
setOrigin n t = (GenType (typeOfGT t) $ mkOrigin n)

remComment :: GenType -> GenType
remComment (GenType t o) = GenType t $ toNoComOrigin o

errType :: String -> FTrav GenType
errType s = return $ genType $ CS.TCon ("err-" ++ s) [] markUnbox

stripOrigT :: GenType -> RawType
stripOrigT = RT . fmap stripOrigT . ffmap (const $ CS.RE CS.Unitel) . typeOfGT

