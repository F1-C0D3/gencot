{-# LANGUAGE PackageImports #-}
module Gencot.Cogent.Translate where

import Control.Monad (liftM,when)
import Data.List (nub,isPrefixOf,isInfixOf)
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
import Gencot.Items (ItemAssocType,isSafePointerItem,getIndividualItemId,getTagItemId,derivedItemIds,getIndividualItemAssoc,getTypedefItemAssoc,adjustItemAssocType,getMemberSubItemAssoc,getRefSubItemAssoc,getResultSubItemAssoc,getElemSubItemAssoc,getParamSubItemAssoc,getItemAssocTypes,getSubItemAssocTypes)
import Gencot.Cogent.Ast
import Gencot.C.Translate (transStat,transExpr)
import Gencot.Traversal (FTrav,getParmods,markTagAsNested,isMarkedAsNested)
import Gencot.Util.Types (carriedTypes,usedTypeNames,resolveFully,isExtern,isCompOrFunc,isCompPointer,isNamedFunPointer,isFunPointer,isPointer,isAggregate,isFunction,isTypeDefRef,isComplete,isArray,isVoid,isTagRef,containsTypedefs,resolveTypedef,isComposite,isLinearType,isLinearParType,isReadOnlyType,isReadOnlyParType,isDerivedType,wrapFunAsPointer,getTagDef)
import Gencot.Json.Identifier ()

genType t = GenType t noOrigin

-- | Translate a sequence of C "external" (global) declarations to a sequence of Cogent toplevel definitions.
transGlobals :: [LCA.DeclEvent] -> FTrav [GenToplv]
transGlobals tcs = liftM concat $ mapM transGlobal tcs

-- | Translate a C "external" (global) declaration to a sequence of Cogent toplevel definitions.
-- A single C declaration with nested declarations may be translated to a sequence of Cogent definitions.
transGlobal :: LCA.DeclEvent -> FTrav [GenToplv]
-- Translate a C struct definition -> see transStruct
transGlobal (LCA.TagEvent (LCA.CompDef ct@(LCA.CompType sueref LCA.StructTag _ _ _))) =
    transStruct (getTagItemId sueref LCA.StructTag) ct transMember
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
transGlobal (LCA.DeclEvent decl@(LCA.Declaration (LCA.Decl _ n))) | isComplete $ LCA.declType decl = do
    f <- transObjName idnam 
    sfn <- srcFileName idnam
    let iat = getIndividualItemAssoc decl sfn
    t <- transType False iat
    return $ wrapOrigin n ([GenToplv (CS.AbsDec f (CS.PT [] $ mkFunType t)) noOrigin])
    where idnam = LCA.declIdent decl
-- Translate a C function definition of the form
-- > rt name(parlist) { stmt }
-- to a Cogent function definition of the form
-- > name :: (partypes) -> rt
-- > name (parnames) = dummy {- stmt -}
-- where @partypes@, @rt@, and @dummy@ are modified according to a parameter modification description
-- and stmt is translated by mapping all non-local names.
transGlobal (LCA.DeclEvent idecl@(LCA.FunctionDef fdef@(LCA.FunDef decl stat n))) = do
    f <- transObjName idnam
    sfn <- srcFileName idnam
    let iat = getIndividualItemAssoc idecl sfn
    t <- transType False iat
    ps <- transParamNames isVar pars
    LCA.enterFunctionScope
    LCA.defineParams LCN.undefNode decl
    d <- dummyExpr res
    d <- extendExpr idecl d pars
    s <- transStat stat
    LCA.leaveFunctionScope
    return $ wrapOrigin n ([GenToplv (CS.FunDef f (CS.PT [] t) [CS.Alt ps CCS.Regular $ FunBody d s]) noOrigin])
    where idnam = LCA.declIdent idecl
          (LCA.FunctionType (LCA.FunType res pars isVar) _) = LCA.declType idecl
-- Translate a C object definition of the form
-- > typ name = expr;
-- (where type may be a derived type syntactically integrated in the name)
-- to a Cogent abstract function definition of the form
-- > name :: () -> typ
-- for a parameterless access function
transGlobal (LCA.DeclEvent odef@(LCA.ObjectDef (LCA.ObjDef _ _ n))) = do
    f <- transObjName idnam
    sfn <- srcFileName idnam
    let iat = getIndividualItemAssoc odef sfn
    t <- transType False iat
    return $ wrapOrigin n ([GenToplv (CS.AbsDec f (CS.PT [] $ mkFunType t)) noOrigin])
    where idnam = LCA.declIdent odef
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
-- If the @type-specifier@ denotes a struct or union type the typedef is first adjusted to the derived pointer type.
-- Array types need no adjusting, they are always adjusted by @transType@.
-- The translation result has the form
-- > type idnam = type
-- where @type@ is constructed by translating @type-specifier@ and applying all derivations from the adjusted @declarator@.
-- A MayNull application to type is removed.
transGlobal (LCA.TypeDefEvent (LCA.TypeDef idnam typ _ n)) = do
    t <- transType False modifiat
    nt <- transTagIfNested iat n
    return $ wrapOrigin n (nt ++ [GenToplv (CS.TypeDec tn [] (rmMayNull t)) noOrigin])
    where tn = mapNameToUpper idnam
          iat = getTypedefItemAssoc idnam typ
          modifiat = if isComposite typ then adjustItemAssocType iat else iat
        
transGlobal _ = return $ [GenToplv (CS.Include "err-unexpected toplevel") noOrigin]

transExtGlobals :: [String] -> [LCA.DeclEvent] -> FTrav [GenToplv]
transExtGlobals tds tcs = liftM concat $ mapM (transExtGlobal tds) tcs

-- | Translate an external declaration (from a system include file) to a sequence of Cogent toplevel definitions.
-- For typedefs and composite type members the type is fully resolved.
-- Otherwise the translation is performed as usual.
-- The additional first parameter is a list of type names where to stop resolving.
transExtGlobal :: [String] -> LCA.DeclEvent -> FTrav [GenToplv]
transExtGlobal tds (LCA.TypeDefEvent (LCA.TypeDef idnam typ _ n)) = do
    t <- transType False modifiat
    nt <- transTagIfNested resiat n
    return $ wrapOrigin n (nt ++ [GenToplv (CS.TypeDec tn [] (rmMayNull t)) noOrigin])
    where tn = mapNameToUpper idnam
          resiat = getTypedefItemAssoc idnam $ resolveFully tds typ
          modifiat = if isComposite typ then adjustItemAssocType resiat else resiat
transExtGlobal tds (LCA.TagEvent (LCA.CompDef ct@(LCA.CompType sueref LCA.StructTag _ _ _))) = 
    transStruct (getTagItemId sueref LCA.StructTag) ct (transExtMember tds)
transExtGlobal _ e = transGlobal e

-- | If not yet translated as nested, translate a C struct definition of the form
-- > struct tagname { ... }
-- to a Cogent record definition of the form
-- > type Struct_tagname = { ... }
-- The first parameter is the item identifier of the item where the struct type is used.
-- It is only needed for anonymous structs which can be used by a single item only.
-- The third parameter is a monadic action which translates a single member declaration
-- to a pair of Cogent field name and type. As additional first parameter it expects the reference
-- to the C struct type definition.
-- All nested tag definitions are translated and appended as separate toplevel type definitions.
transStruct :: String -> LCA.CompType -> (ItemAssocType -> LCA.MemberDecl -> FTrav (CCS.FieldName, (GenType, CS.Taken))) -> FTrav [GenToplv]
transStruct iid (LCA.CompType sueref LCA.StructTag mems _ n) trMember = do
    nst <- isMarkedAsNested sueref
    if nst 
       then return []
       else do
           tn <- transTagName typnam
           ms <- mapM (trMember iat) aggmems
           nts <- liftM concat $ mapM (transMemTagIfNested iat) aggmems
           return $ wrapOrigin n ([GenToplv (CS.TypeDec tn [] $ genType $ CS.TRecord ms markBox) noOrigin] ++ nts)
    where siid = if LCI.isAnonymousRef sueref then iid else getTagItemId sueref LCA.StructTag
          typnam = LCA.TyComp $ LCA.CompTypeRef sueref LCA.StructTag n
          iat = (siid,LCA.DirectType typnam LCA.noTypeQuals LCA.noAttributes)
          aggmems = aggBitfields mems

-- | Translate nested tag definitions in a member definition.
-- The first argument is the ItemAssocType of the struct.
transMemTagIfNested :: ItemAssocType -> LCA.MemberDecl -> FTrav [GenToplv]
transMemTagIfNested iat mdecl = transTagIfNested (getMemberSubItemAssoc iat mdecl) $ LCN.nodeInfo mdecl

-- | Translate a C type as nested tag definition together with all contained nested tag definitions.
-- The type is specified as an ItemAssocType. The item id is used for tagless struct, union, and enums.
-- Additional second parameter is the position where the type is used.
-- If the type is a reference to a struct,union, or enum, lookup its definition.
-- If the definition's position is nested in the position where the type is used, then
-- the definition is nested at that position. Translate it and mark it as nested in the user state.
transTagIfNested :: ItemAssocType -> LCN.NodeInfo -> FTrav [GenToplv]
transTagIfNested (iid, typ@(LCA.DirectType tn _ _)) n | isTagRef typ = do
    dt <- LCA.getDefTable
    let mtd = getTagDef dt $ getSUERef tn
    case mtd of
         Nothing -> return []
         Just td -> 
            if isNested (nodeInfo td) n 
               then do
                   ng <- case td of
                              LCA.CompDef ct@(LCA.CompType _ LCA.StructTag _ _ _) -> transStruct iid ct transMember
                              _ -> transGlobal $ LCA.TagEvent td
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
-- abstract types used for function pointer types to the original ItemAssocType.
-- The String list @tdn@ contains typedef names where to stop resolving external typedef names.
--
-- Retrieve the ItemAssocTypes carried by @tc@, get all sub-ItemAssocTypes,
-- add all fully resolved forms (without stopping at @tdn@) for function pointer equivalence definitions
-- reduce to derived array and function pointer types, 
-- translate the types to Cogent, and retrieve their names.
genDerivedTypeNames :: [String] -> LCA.DeclEvent -> FTrav [Map String ItemAssocType]
genDerivedTypeNames tdn tc = do
    iats <- getItemAssocTypes tdn tc
    iats <- (liftM concat) $ mapM getSubItemAssocTypes iats
    let fiats = filter (\(_,t) -> (isDerivedType t) && (not $ isFunction t) && ((not $ isPointer t) || isFunPointer t)) 
                $ concat $ map (\(iid,t) -> nub [(iid,t), (iid,resolveFully [] t)]) iats
    mapM (\iat -> do gt <- transType False iat; return $ singleton (getName gt) iat) fiats
--    sfn <- srcFileName tc
--    liftM (map (\(gt,iid,t) -> singleton (getName gt) (iid,t))) $ 
--        mapM (\(iid,t) -> do gt <- transType False iid t; return (gt,iid,t)) $ 
--        filter (\(_,t) -> isArray t || (isFunPointer t && (not $ isTypeDefRef t))) $
--       nub $ map (\idandt -> wrapFunAsPointer idandt) $ 
--        concat $ map (\(iid,t) -> nub [(iid,t), (iid,resolveFully [] t)]) $
--        concat $ map (uncurry getDerivedParts) $ carriedWithItemId sfn tdn tc
    where getName (GenType (CS.TCon nam _ _) _) = nam

-- | Generate type definitions for a Cogent type name @nam@ used by a derived array or function pointer type.
-- Additional argument is the original C type as an ItemAssocType.
genDerivedTypeDefs :: String -> ItemAssocType -> FTrav [GenToplv]
-- For a derived array type the name has the form @CArr<size>@, @CArrX<size>X@ or @CArrXX@.
-- The last case is ignored.
-- For the other cases two generic type defintions are generated of the form
-- > type CArr... el = { arr: #(UArr... el) }
-- > type UArr... el
genDerivedTypeDefs nam (_,(LCA.ArrayType _ _ _ _)) | arrDerivHasSize nam =
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
genDerivedTypeDefs nam iat@(iid,pt@(LCA.PtrType t _ _)) = do
    rslvtyp <- transType True iat
    let tdef = if getName rslvtyp == nam
                then CS.AbsTypeDec nam [] []
                else CS.TypeDec nam [] rslvtyp
    typ <- transType False $ getRefSubItemAssoc iat t
    let fdef = GenToplv (CS.TypeDec fnam [] typ ) noOrigin
    return $ (GenToplv tdef noOrigin): if (mapFunDeriv True) `isPrefixOf` nam then [fdef] else []
    where fnam = "CFun" ++ (drop (length (mapFunDeriv True)) nam)
          getName (GenType (CS.TCon nam _ _) _) = nam
genDerivedTypeDefs _ _ = return []

extendExpr :: LCA.IdentDecl -> RawExpr -> [LCA.ParamDecl] -> FTrav RawExpr
extendExpr fdef e pars = do
    sfn <- srcFileName $ LCA.declIdent fdef
    pms <- getParmods $ getIndividualItemId fdef sfn
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
-- First parameter is the ItemAssocType of the enclosing struct type.
transMember :: ItemAssocType -> LCA.MemberDecl -> FTrav (CCS.FieldName, (GenType, CS.Taken))
transMember iat mdecl@(LCA.MemberDecl (LCA.VarDecl (LCA.VarName idnam _) _ typ) _ n) =
    transMemberDef idnam (getMemberSubItemAssoc iat mdecl) n
{- LCA.AnonBitField cannot occur since it is always replaced by aggBitfields -}

-- | Translate external struct member definition to pair of Cogent record field name and type.
-- The member type is fully resolved.
-- The additional first parameter is a list of type names where to stop resolving.
transExtMember :: [String] -> ItemAssocType -> LCA.MemberDecl -> FTrav (CCS.FieldName, (GenType, CS.Taken))
transExtMember tds iat mdecl@(LCA.MemberDecl (LCA.VarDecl (LCA.VarName idnam _) _ typ) _ n) =
    transMemberDef idnam (iid,resolveFully tds typ) n
    where (iid,typ) = getMemberSubItemAssoc iat mdecl

-- | Translate struct member definition to pair of Cogent record field name and type.
-- Translate member type, if array set unboxed. Map member name if it starts with uppercase.
transMemberDef :: LCI.Ident -> ItemAssocType -> LCN.NodeInfo -> FTrav (CCS.FieldName, (GenType, CS.Taken))
transMemberDef idnam iat@(_,typ) n = do
    t <- transType False iat
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
-- The C type is specified as an ItemAssocType, so that its item properties can be respected.
-- The first parameter specifies whether typedef names shall be resolved.
transType :: Bool -> ItemAssocType -> FTrav GenType 

-- Type void:
-- Translate to: ()
transType _ (_, (LCA.DirectType LCA.TyVoid _ _)) = 
    return $ genType CS.TUnit
-- Direct type:
-- Translate to: Name of primitive type (boxed) or composite type (unboxed).
-- Remark: Semantically, primitive types are unboxed. 
-- However, if marked as unboxed the Cogent prettyprinter adds a (redundant) unbox operator.
transType _ (_, (LCA.DirectType tnam _ _)) = do
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
transType rslv iat@(iid, (LCA.TypeDefType (LCA.TypeDefRef idnam typ _) _ _)) = do
    safe <- isSafePointerItem iat
    rslvtyp <- transType True $ getTypedefItemAssoc idnam typ
    if rslv
       then return $ rmMayNullIf safe rslvtyp
       else return $ addMayNullIfNot (safe || (not $ hasMayNull rslvtyp)) rtyp
    where tn = mapNameToUpper idnam
          ub = if (isCompOrFunc typ) || (isFunPointer typ) then markUnbox else markBox
          rtyp = genType $ CS.TCon tn [] ub
-- Pointer to void:
-- Translate to: CVoidPtr
-- If not safe pointer: MayNull CVoidPtr
transType _ iat@(iid, (LCA.PtrType t _ _)) | isVoid t = do
    safe <- isSafePointerItem iat
    return $ addMayNullIfNot safe $ genType $ CS.TCon mapPtrVoid [] markBox
-- Derived pointer type for function type t:
-- Encode t, apply CFunPtr or CFunInc and make unboxed.
transType rslv iat@(_, (LCA.PtrType t _ _)) | isFunction t = do
    enctyp <- encodeType rslv $ getRefSubItemAssoc iat t
    return $ genType $ CS.TCon ((mapFunDeriv $ isComplete t) ++ "_" ++ enctyp) [] markUnbox
-- Derived pointer type for array type t:
-- Translate t and use as result. Always boxed.
-- If not safe pointer: apply MayNull
transType rslv iat@(iid, (LCA.PtrType t _ _)) | isArray t = do
    safe <- isSafePointerItem iat
    typ <- transType rslv $ getRefSubItemAssoc iat t
    return $ addMayNullIfNot safe typ
-- Derived pointer type for other type t:
-- Translate t. If unboxed and no function pointer make boxed, otherwise apply CPtr. Always boxed.
-- If not safe pointer apply MayNull.
transType rslv iat@(iid, pt@(LCA.PtrType t _ _)) = do
    safe <- isSafePointerItem iat
    typ <- transType rslv $ getRefSubItemAssoc iat t
    let rtyp = if (isUnboxed typ) && not (isFunPointer t) 
                then setBoxed typ
                else genType $ CS.TCon mapPtrDeriv [typ] markBox
    return $ addMayNullIfNot safe rtyp
-- Complete derived function type: ret (p1,..,pn)
-- Translate to: Cogent function type (p1,..,pn) -> ret, then apply parmod description.
transType rslv iat@(iid, t@(LCA.FunctionType (LCA.FunType ret pars variadic) _)) = do
    r <- transType rslv $ getResultSubItemAssoc iat ret
    ps <- mapM (transParamType rslv iat) pars
    let pt = mkParType (ps ++ if variadic then [variadicType] else [])
    applyParmods t iid $ genType $ CS.TFun pt r
-- Derived array type for element type t:
-- Translate t, if again array type apply unbox operator, then apply generic array type. Always boxed.
transType rslv iat@(_, (LCA.ArrayType t as _ _)) = do
    typ <- transType rslv $ getElemSubItemAssoc iat t
    return $ genType $ CS.TCon (mapArrDeriv as) [if isArray t then setUnboxed typ else typ] markBox 

-- | Encode a C type specification as a Cogent type name.
-- The C type is specified as an ItemAssocType, so that its item properties can be respected.
-- The first parameter specifies whether typedef names shall be resolved.
encodeType :: Bool -> ItemAssocType -> FTrav String
-- Type void:
-- Encode as: Void
encodeType _ (_, (LCA.DirectType LCA.TyVoid _ _)) = 
    return "Void"
-- Direct type:
-- Encode as: Name of primitive type or composite type.
-- For composite type prepend unbox step.
encodeType _ (_, (LCA.DirectType tnam _ _)) = do
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
encodeType rslv iat@(iid, (LCA.TypeDefType (LCA.TypeDefRef idnam typ _) _ _)) = do
    safe <- isSafePointerItem iat
    rslvtyp <- encodeType True $ getTypedefItemAssoc idnam typ
    if rslv
       then return $ rmMayNullStepIf safe rslvtyp
       else return $ addMayNullStepIfNot (safe || (not $ hasMayNullStep rslvtyp)) rtyp
    where tn = mapNameToUpper idnam
          ustep = if isAggregate typ then mapUboxStep else ""
          rtyp = (ustep ++ tn)
-- Derived pointer type for function type t:
-- Encode t, prepend pointer derivation step.
encodeType rslv iat@(_, (LCA.PtrType t _ _)) | isFunction t = do
    tn <- encodeType rslv $ getRefSubItemAssoc iat t
    return (mapPtrStep ++ tn)
-- Derived pointer type for other type t:
-- Encode t, for aggregate type remove unbox step, otherwise prepend pointer derivation step.
-- If not a safe pointer, add MayNull step.
encodeType rslv iat@(iid, pt@(LCA.PtrType t _ _)) = do
    safe <- isSafePointerItem iat
    tn <- encodeType rslv $ getRefSubItemAssoc iat t
    let htn = if isAggregate t then (rmUboxStep tn) else (mapPtrStep ++ tn)
    return $ addMayNullStepIfNot safe htn
-- Complete derived function type: ret (p1,..,pn)
-- Encode ret, prepend function derivation step using encoded pi.
encodeType rslv iat@(iid, (LCA.FunctionType (LCA.FunType ret pars variadic) _)) = do
    tn <- encodeType rslv $ getResultSubItemAssoc iat ret
    encpars <- mapM (encodeParamType rslv iat) pars
    pms <- getParamMods iid pars variadic
    let vencpars = if variadic then encpars ++ [variadicTypeName] else encpars
    let ps = map applyEncodeParmod $ zip pms vencpars
    return ((mapFunStep ps) ++ tn)
-- Incomplete derived function type: ret ()
-- Encode ret, prepend incomplete function derivation step.
encodeType rslv iat@(_, (LCA.FunctionType (LCA.FunTypeIncomplete ret) _)) = do
    tn <- encodeType rslv $ getResultSubItemAssoc iat ret
    return (mapIncFunStep ++ tn)
-- Derived array type for element type t:
-- Encode t using function id only if pointer type, prepend array derivation step and unbox step.
encodeType rslv iat@(iid, (LCA.ArrayType t as _ _)) = do
    tn <- encodeType rslv $ getElemSubItemAssoc iat t
    return (mapUboxStep ++ (mapArrStep as) ++ tn)

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
getTag (LCA.DirectType (LCA.TyComp (LCA.CompTypeRef sueref knd _)) _ _) = 
    kndstr ++ "|" ++ (sueRefToString sueref)
    where kndstr = case knd of
                    LCA.StructTag -> "struct"
                    LCA.UnionTag -> "union"
getTag (LCA.DirectType (LCA.TyEnum (LCA.EnumTypeRef sueref _)) _ _) = 
    "enum|" ++ (sueRefToString sueref)
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
    --when ("struct|pmd" `isPrefixOf` fid) $ error ("fid: " ++ fid)
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
applyToPars pts = mkParType $ map applyToPar pts

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
applyToRes pts rt = mkParType $ addrps rt
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
mkFunType t = genType $ CS.TFun (mkParType []) t

variadicType = genType (CS.TCon variadicTypeName [] markBox)
variadicTypeName = "VariadicCogentParameters"

-- | Translate a C parameter declaration to the adjusted Cogent parameter type.
-- The first argument specifies whether typedef names shall be resolved.
-- The second argument is the function's ItemAssocType.
transParamType :: Bool -> ItemAssocType -> LCA.ParamDecl -> FTrav GenType
transParamType rslv iat pd = do
    t <- transType rslv $ getParamSubItemAssoc iat pd
    return $ GenType (typeOfGT t) $ origin pd

-- | Encode a type as parameter type.
-- For an array type: adjust by removing unbox step.
-- For a function type: adjust by adding pointer step.
encodeParamType :: Bool -> ItemAssocType -> LCA.ParamDecl -> FTrav String
encodeParamType rslv iat pd = do
    typ <- encodeType rslv $ getParamSubItemAssoc iat pd
    if isArray $ LCA.declType pd
       then return $ rmUboxStep typ
       else return typ

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

-- | Construct a function's parameter type from the sequence of translated C parameter types.
-- The result is either the unit type, a single type, or a tuple type (for more than 1 parameter).
mkParType :: [GenType] -> GenType
mkParType [] = genType CS.TUnit
mkParType [gt] = gt
mkParType gts = genType $ CS.TTuple gts 

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

