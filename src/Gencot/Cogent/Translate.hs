{-# LANGUAGE PackageImports #-}
module Gencot.Cogent.Translate where

import Control.Monad (liftM,filterM,when)
import Data.List as L (nub,isPrefixOf,isInfixOf,intercalate,unlines,sortOn,sort,intersect,union)
import Data.Map as M (Map,singleton,unions,toList,union)
import Data.Maybe (catMaybes,fromJust)

import Data.Char (ord)

import "language-c" Language.C as LC hiding (pretty,Pretty)
import Language.C.Data.Ident as LCI
import Language.C.Data.Node as LCN
import Language.C.Data.Position as LCP
import Language.C.Analysis as LCA
import Language.C.Analysis.DefTable as LCD
import Language.C.Analysis.AstAnalysis (tExpr, ExprSide(RValue), StmtCtx(LoopCtx)) -- sollte auch über LCA ansprechbar sein
import Language.C.Syntax.AST as LCS

import Cogent.Surface as CS
import Cogent.Common.Syntax as CCS
import Cogent.Common.Types as CCT

import Gencot.Origin (Origin, noOrigin, origin, mkOrigin, noComOrigin, mkBegOrigin, mkEndOrigin, prepOrigin, appdOrigin, isNested, toNoComOrigin)
import Gencot.Names (
  transTagName, transObjName, mapIfUpper, mapNameToUpper, mapNameToLower, mapPtrDeriv, mapPtrVoid, mapMayNull, mapArrDeriv, mapFunDeriv, 
  arrDerivHasSize, arrDerivCompNam, arrDerivToUbox, mapUboxStep, rmUboxStep, mapMayNullStep, rmMayNullStepThroughRo, addMayNullStep, 
  mapPtrStep, mapFunStep, mapIncFunStep, mapArrStep, mapModStep, mapRoStep, mapNamFunStep,
  getFileName, globStateType, isNoFunctionName, heapType, heapParamName, variadicParamName)
import Gencot.Items.Types (
  ItemAssocType, isNotNullItem, isReadOnlyItem, isNoStringItem, isHeapUseItem, getItemProperties,
  getIndividualItemId, getObjectItemId, getParamSubItemId,
  getGlobalStateProperty, makeGlobalStateParams, getTagItemAssoc, getIndividualItemAssoc, getTypedefItemAssoc, adjustItemAssocType, 
  getMemberSubItemAssoc, getRefSubItemAssoc, getResultSubItemAssoc, getElemSubItemAssoc, getParamSubItemAssoc, 
  getItemAssocType, getMemberItemAssocTypes, getSubItemAssocTypes, numberList, getAddResultProperties, getFunctionProperties)
import Gencot.Items.Identifier (getObjFuncName, getParamName)
import Gencot.Cogent.Ast
import Gencot.Cogent.Bindings (
  BindsPair, valVar, leadVar, lvalVar, resVar, 
  mkEmptyBindsPair, mkDummyBindsPair, mkUnitBindsPair, mkDefaultBindsPair, mkIntLitBindsPair, mkCharLitBindsPair, mkStringLitBindsPair,
  mkValVarBindsPair, mkMemBindsPair, mkIdxBindsPair, mkOpBindsPair, mkAppBindsPair, mkAssBindsPair, mkIfBindsPair, concatBindsPairs, 
  processMFpropForBindsPairs,
  replaceBoundVarType,
  mkDummyBinding, mkNullBinding, mkExpBinding, mkRetBinding, mkBreakBinding, mkContBinding, 
  mkIfBinding, mkSwitchBinding, mkCaseBinding, mkSeqBinding, mkDecBinding, mkForBinding,
  processMFpropForPatterns)
import Gencot.Cogent.Expr (mkUnitExpr, mkVarExpr, mkBodyExpr, mkPlainExpr)
import Gencot.Cogent.Postproc (postproc)
import qualified Gencot.C.Ast as LQ (Stm(Exp,Block), Exp)
import qualified Gencot.C.Translate as C (transStat, transExpr, transArrSizeExpr, transBlockItem)
import Gencot.Traversal (
  FTrav, markTagAsNested, isMarkedAsNested, hasProperty, stopResolvTypeName, 
  setFunDef, clrFunDef, enterItemScope, leaveItemScope, registerItemId, nextVarNum, resetVarNums,
  getValCounter, getCmpCounter, resetVarCounters, resetValCounter, getTConf)
import Gencot.Util.Types (
  carriedTypes, isExtern, isCompOrFunc, isCompPointer, isNamedFunPointer, isFunPointer, isPointer, isAggregate, isFunction, 
  isTypeDefRef, isComplete, isArray, isVoid, isTagRef, containsTypedefs, resolveTypedef, isComposite, 
  isLinearType, isLinearParType, isReadOnlyType, isReadOnlyParType, isDerivedType, isExternTypeDef, wrapFunAsPointer, getTagDef)
import Gencot.Util.Expr (checkForTrans, getFreeInCExpr, getFreeInCStat)

genType t = GenType t noOrigin
genExpr e = GenExpr e noOrigin Nothing

-- | Translate a sequence of C "external" (global) declarations to a sequence of Cogent toplevel definitions.
transGlobals :: [LCA.DeclEvent] -> FTrav [GenToplv]
transGlobals tcs = liftM concat $ mapM transGlobal tcs

-- | Translate a C "external" (global) declaration to a sequence of Cogent toplevel definitions.
-- A single C declaration with nested declarations may be translated to a sequence of Cogent definitions.
transGlobal :: LCA.DeclEvent -> FTrav [GenToplv]
-- | If not yet translated as nested, translate a C struct definition of the form
-- > struct tagname { ... }
-- to a Cogent record definition of the form
-- > type Struct_tagname = { ... }
-- All nested tag definitions are translated and appended as separate toplevel type definitions.
transGlobal (LCA.TagEvent def@(LCA.CompDef (LCA.CompType sueref LCA.StructTag mems _ n))) = do
    nst <- isMarkedAsNested sueref
    if nst 
       then return []
       else do
           tn <- transTagName typnam
           sfn <- getFileName
           let iat = getTagItemAssoc def sfn
           ms <- mapM (transMember iat) aggmems
           nts <- liftM concat $ mapM (transMemTagIfNested iat) aggmems
           return $ wrapOrigin n ([GenToplv (CS.TypeDec tn [] $ genType $ CS.TRecord CCT.NonRec ms markBox) noOrigin] ++ nts)
    where typnam = LCA.TyComp $ LCA.CompTypeRef sueref LCA.StructTag n
          aggmems = aggBitfields mems
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
-- (where typ may be a derived type syntactically integrated in the name)
-- to a Cogent abstract function definition of the form
-- > name : funtyp
-- If the C object is not a function, the Cogent function is a parameterless
-- access function of type () -> typ
transGlobal de@(LCA.DeclEvent decl@(LCA.Declaration (LCA.Decl _ n))) | isComplete dtyp = do
    f <- transObjName idnam 
    sfn <- getFileName
    let iat = getIndividualItemAssoc decl sfn
    t <- transType False iat
-- from nesttags:
--    nt <- transTagIfNested dtyp n
    let typ = if isFunction dtyp then t else mkFunType t
    if isFunction dtyp -- suppress generation of access function
       then return $ wrapOrigin n ({-nt ++ -}[GenToplv (CS.AbsDec f (CS.PT [] [] typ)) noOrigin])
       else return $ []
    where idnam = LCA.declIdent decl
          dtyp = LCA.declType decl
-- Translate a C function definition of the form
-- > rt name(parlist) { stmt }
-- to a Cogent function definition of the form
-- > name :: (partypes) -> rt
-- > name (parnames) = expr
-- where @expr@ is the translation of @stmt@ and
-- @partypes@, @rt@, and @expr@ are modified according to a parameter modification description.
transGlobal (LCA.DeclEvent idecl@(LCA.FunctionDef (LCA.FunDef decl stat n))) = do
    f <- transObjName $ LCA.declIdent idecl
    sfn <- getFileName
    let iat@(fid,_) = getIndividualItemAssoc idecl sfn
    t <- transType False iat
-- from nesttags:
--    nt <- transTagIfNested typ n -- wirkt erst wenn transTagIfNested auch derived types verarbeitet
    ps <- transParamNames iat isVar pars
    LCA.enterFunctionScope
    LCA.defineParams LCN.undefNode decl
    enterItemScope
    registerParamIds pars 1 fid
    setFunDef idecl
    e <- transBody iat stat pars
--    e <- extendExpr iat e pars
    clrFunDef
    resetVarNums
    leaveItemScope
    LCA.leaveFunctionScope
    return $ wrapOrigin n ({-nt ++ -}[GenToplv (CS.FunDef f (CS.PT [] [] t) [CS.Alt ps CCS.Regular e]) noOrigin])
    where typ@(LCA.FunctionType (LCA.FunType res pars isVar) _) = LCA.declType idecl
-- Translate a C object definition of the form
-- > typ name = expr;
-- (where typ may be a derived type syntactically integrated in the name).
-- If it has a Global-State property a type synonym definition of the form
-- > type GlobState<i> = typ*
-- is generated for the type of pointer to the object. 
-- If it has a Const-Val property a Cogent abstract function definition of the form
-- > name :: () -> typ
-- for a parameterless access function is generated.
transGlobal (LCA.DeclEvent odef@(LCA.ObjectDef (LCA.ObjDef _ _ n))) = do
    f <- transObjName idnam
    sfn <- getFileName
    let iat = getIndividualItemAssoc odef sfn
    gs <- getGlobalStateProperty $ fst iat
    tsyn <- if null gs 
               then return $ []
               else do
                   pt <- transType False $ adjustItemAssocType iat
                   return $ [GenToplv (CS.TypeDec (globStateType gs) [] $ rmMayNullIf True pt) noOrigin]
    t <- transType False iat
-- from nesttags:
--    nt <- transTagIfNested dtyp n
    let afun = [] -- [GenToplv (CS.AbsDec f (CS.PT [] [] $ mkFunType t)) noOrigin]
    return $ wrapOrigin n ({-nt ++ -} tsyn ++ afun)
    where idnam = LCA.declIdent odef
          dtyp = LCA.declType odef
-- Translate a C enumerator definition of the form
-- > name = expr;
-- to a Cogent constant definition of the form
-- > name :: U32
-- > name = exp
-- where @exp@ is the translation of expr.
transGlobal (LCA.DeclEvent (LCA.EnumeratorDef (LCA.Enumerator idnam expr _ n))) = do
    e <- transExpr expr
    en <- mapNameToLower idnam
    return $ [GenToplv (CS.ConstDef en (genType $ CS.TCon "U32" [] markUnbox) e) $ mkOrigin n]
-- Translate a typedef of the form
-- > typedef type-specifier declarator;
-- where @declarator@ denotes a (derived type for an) identifier @idnam@.
-- If the @type-specifier@ denotes a struct or union type the typedef is first adjusted to the derived pointer type.
-- Array types need no adjusting, they are always adjusted by @transType@.
-- The translation result has the form
-- > type idnam = type
-- where @type@ is constructed by translating @type-specifier@ and applying all derivations from the adjusted @declarator@.
-- A MayNull application to @type@ is removed.
-- If @type@ is an array type or translates to type String, a Bang operator is also removed.
transGlobal (LCA.TypeDefEvent (LCA.TypeDef idnam typ _ n)) = do
    t <- transType False modifiat
    nt <- transTagIfNested iat n
    let dt = if isArray typ || isString t then rmReadOnly $ rmMayNullThroughBang t else rmMayNullThroughBang t
    tn <- mapNameToUpper idnam
    return $ wrapOrigin n (nt ++ [GenToplv (CS.TypeDec tn [] dt) noOrigin])
    where iat = getTypedefItemAssoc idnam typ
          modifiat = if isComposite typ then adjustItemAssocType iat else iat
        
transGlobal _ = return $ [GenToplv (CS.Include "err-unexpected toplevel") noOrigin]

registerParamIds :: [LCA.ParamDecl] -> Int -> String -> FTrav ()
registerParamIds [] _ _ = return ()
registerParamIds (p : ps) pos fid = do
    registerItemId (LCI.identToString $ LCA.declIdent p) $ getParamSubItemId fid (pos,p)
    registerParamIds ps (pos+1) fid

-- | Translate nested tag definitions in a member definition.
-- The first argument is the ItemAssocType of the struct.
transMemTagIfNested :: ItemAssocType -> LCA.MemberDecl -> FTrav [GenToplv]
transMemTagIfNested iat mdecl = transTagIfNested (getMemberSubItemAssoc iat mdecl) $ LCN.nodeInfo mdecl

-- | Translate a C type as nested tag definition together with all contained nested tag definitions.
-- The type is specified as an ItemAssocType.
-- Additional second parameter is the position where the type is used.
-- If the type is a reference to a struct,union, or enum, lookup its definition.
-- If the definition's position is nested in the position where the type is used, then
-- the definition is nested at that position. Translate it and mark it as nested in the user state.
transTagIfNested :: ItemAssocType -> LCN.NodeInfo -> FTrav [GenToplv]
transTagIfNested (_, typ@(LCA.DirectType tn _ _)) n | isTagRef typ = do
    dt <- LCA.getDefTable
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
genTypeDefs :: [LCA.DeclEvent] -> FTrav [GenToplv]
genTypeDefs tcs = do
    derivedTypes <- liftM (unions . concat) $ mapM genDerivedTypeNames tcs
    (liftM concat) $ mapM (uncurry genDerivedTypeDefs) $ toList derivedTypes

-- | Construct all names of derived array and function pointer types occurring in a type carrier @tc@.
-- The result is a map from names of generic types used for mapped array types and names of
-- abstract types used for function pointer types to the original ItemAssocType.
--
-- Retrieve the ItemAssocTypes carried by @tc@, get all sub-ItemAssocTypes,
-- add all fully resolved forms (without stopping at stop-resolve names) for function pointer equivalence definitions
-- reduce to derived array and function pointer types, 
-- translate the types to Cogent, and retrieve their names.
genDerivedTypeNames :: LCA.DeclEvent -> FTrav [Map String ItemAssocType]
genDerivedTypeNames tc = do
    iat <- getItemAssocType tc
    miats <- getMemberItemAssocTypes tc
    iats <- (liftM concat) $ mapM getSubItemAssocTypes (iat : miats)
    let fiats = filter (\(_,t) -> (isDerivedType t) && (not $ isFunction t) && ((not $ isPointer t) || isFunPointer t)) iats
    mapM genMap fiats
    where getName (GenType (CS.TCon nam _ _) _) = nam
          getName (GenType (CS.TBang (GenType (CS.TCon nam _ _) _)) _) = nam
          genMap :: ItemAssocType -> FTrav (Map String ItemAssocType)
          genMap iat = do
              gt <- transType False iat
              rgt <- transType True iat
              return $ M.union (singleton (getName gt) iat) (singleton (getName rgt) iat)

-- | Generate type definitions for a Cogent type name @nam@ used by a derived array or function pointer type.
-- Additional argument is the original C type as an ItemAssocType.
genDerivedTypeDefs :: String -> ItemAssocType -> FTrav [GenToplv]
-- For a derived array type the name has the form @CArr<size>@, @CArrX<size>X@ or @CArrXX@.
-- The last case is ignored.
-- For the other cases a generic type defintion is generated of the form
-- > type CArr... el = { arr...: el#[<size>] }
genDerivedTypeDefs nam (_,(LCA.ArrayType _ as _ _)) | arrDerivHasSize nam = do
    e <- transExpr $ getSizeExpr as
    let atyp = genType $ CS.TArray (genType $ CS.TVar "el" False False) e markUnbox []
    return [GenToplv (CS.TypeDec nam ["el"] $ genType $ CS.TRecord CCT.NonRec [(arrDerivCompNam nam, (atyp, False))] markBox) noOrigin]
    where getSizeExpr (LCA.ArraySize _ e) = e -- arrDerivHasSize implies that only this case may occur for the array size as.
-- For a derived function pointer type the name has the form @CFunPtr_enc@ or @CFunInc_enc@ where
-- @enc@ is an encoded C type. First we determine the corresponding type where all typedef names are resolved.
-- If that is different from @nam@ then @nam@ contains typedef names. In that case generate a type synonym definition
-- > type nam = resnam
-- where resnam is the name with all typedef names resolved. Otherwise generate an abstract type definition of the form
-- > type nam
-- In the case of a complete function type additionally introduce a synonym for the corresponding
-- function type of the form
-- > type CFun_enc = <Cogent mapping of C function type>
genDerivedTypeDefs nam iat@(iid,pt@(LCA.PtrType _ _ _)) = do
    rslvtyp <- transType True iat
    let isResolved = getName rslvtyp == nam
    let tdef = if isResolved
                then CS.AbsTypeDec nam [] []
                else CS.TypeDec nam [] rslvtyp
    sub <- getRefSubItemAssoc iat
    typ <- transType isResolved sub
    let fdef = GenToplv (CS.TypeDec fnam [] typ ) noOrigin
    return $ (GenToplv tdef noOrigin): if (mapFunDeriv True) `isPrefixOf` nam then [fdef] else []
    where fnam = "CFun" ++ (drop (length (mapFunDeriv True)) nam)
          getName (GenType (CS.TCon nam _ _) _) = nam
genDerivedTypeDefs _ _ = return []

-- | Extend a result expression according to the properties.
-- The Add-Result and Global-State properties of the function parameters 
-- and the Heap-Use property of the function are processed.
-- The first argument is the item associated type of the function.
extendExpr :: ItemAssocType -> GenExpr -> [LCA.ParamDecl] -> FTrav GenExpr
extendExpr iat e pars = do
    pns <- makeResParamNames iat pars
    return $ mkGenExpr $ addres (map (genExpr . CS.Var) pns) e
    where addres res (GenExpr CS.Unitel _ _) = res
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
-- Translate member type, if array set unboxed. Map member name if it starts with uppercase.
transMember :: ItemAssocType -> LCA.MemberDecl -> FTrav (CCS.FieldName, (GenType, CS.Taken))
transMember iat mdecl@(LCA.MemberDecl (LCA.VarDecl (LCA.VarName idnam _) _ _) _ n) = do
    t <- transType False miat
    let ut = if isArray mtyp then setUnboxed (rmReadOnly t) else t
    mnam <- mapIfUpper idnam
    return (mnam, (setOrigin n ut, False))
    where miat@(_,mtyp) = getMemberSubItemAssoc iat mdecl
{- LCA.AnonBitField cannot occur since it is always replaced by aggBitfields -}

-- | Translate a sequence of parameter declarations to a pattern for binding the parameter names.
-- The first argument is the item associated type of the function.
-- The second argument tells whether the function is variadic.
transParamNames :: ItemAssocType -> Bool -> [LCA.ParamDecl] -> FTrav GenPatn
transParamNames fiat variadic pars = do
    pns <- makeParamNames fiat variadic pars
    let porigs = map noComOrigin pars
    let vps = map (\(nam,orig) -> GenIrrefPatn (CS.PVar nam) orig) $ zip pns (porigs ++ (repeat noOrigin))
    return $ if null vps 
                then GenPatn (CS.PIrrefutable $ GenIrrefPatn CS.PUnitel noOrigin) noOrigin 
                else case vps of
                          [pn] -> GenPatn (CS.PIrrefutable pn) noOrigin
                          _ -> GenPatn (CS.PIrrefutable $ GenIrrefPatn (CS.PTuple vps) noOrigin) noOrigin

-- | Construct the list of parameter names for a translated function.
-- The Global-State property of the parameters and the Heap-Use property of the function are processed.
-- The first argument is the item associated type of the function.
-- The second argument tells whether the function is variadic.
makeParamNames :: ItemAssocType -> Bool -> [LCA.ParamDecl] -> FTrav [String]
makeParamNames fiat variadic pars = do
    psn <- mapM (mapIfUpper . LCA.declIdent) pars
    gspars <- makeGlobalStateParams fiat
    let psgn = map (fst . fst) gspars
    huProp <- isHeapUseItem fiat
    let hun = if huProp then [heapParamName (psn ++ psgn)] else []
    let vn = if variadic then [variadicParamName] else []
    return (psn ++ psgn ++ hun ++ vn)

-- | Construct the list of parameter names to be returned as part of the result for a translated function.
-- The properties Add-Result, Global-State, and Read-Only of the parameters 
-- and the Heap-Use property of the function are processed.
-- The first argument is the item associated type of the function.
makeResParamNames :: ItemAssocType -> [LCA.ParamDecl] -> FTrav [String]
makeResParamNames fiat pars = do
    psn <- mapM (mapIfUpper . LCA.declIdent) pars
    arProps <- getAddResultProperties fiat
    let arpsn = map snd $ filter fst $ zip arProps psn
    gspars <- makeGlobalStateParams fiat
    let psgn = map (fst . fst) $ filter snd gspars
    huProp <- isHeapUseItem fiat
    let hun = if huProp then [heapParamName (psn ++ psgn)] else []
    return (arpsn ++ psgn ++ hun)

-- | Translate a C type specification to a Cogent type.
-- The C type is specified as an ItemAssocType, so that its item properties can be respected.
-- The first parameter specifies whether all typedef names shall be resolved.
-- (External types are always resolved until directly used typedef names.)
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
-- If resolving or external typedef where resolve does not stop, translate the referenced type.
-- Otherwise translate to mapped name. Unboxed for struct, union, or function pointer, otherwise boxed.
-- If the typedef name has the Not-Null property, omit or remove MayNull
-- otherwise move a MayNull from the resolved type to the mapped name.
-- If the typedef name has the Read-Only property make the result banged, if the defining type is not String.
transType rslv iat@(iid, (LCA.TypeDefType (LCA.TypeDefRef idnam typ _) _ _)) = do
    dt <- LCA.getDefTable
    srtn <- stopResolvTypeName idnam
    let rslvTypeName = (isExternTypeDef dt idnam) && not srtn
    safe <- isNotNullItem iat
    ro <- isReadOnlyItem iat
    let rslviat = (if not rslvTypeName then getTypedefItemAssoc idnam typ else (iid,typ))
    rslvtyp <- transType rslv rslviat
    tn <- mapNameToUpper idnam
    let nntyp = if rslv || rslvTypeName
                  then rmMayNullIf safe rslvtyp
                  else addMayNullIfNot (safe || (not $ hasMayNull rslvtyp)) $ genType $ CS.TCon tn [] ub
    bang <- if ro then do
        {- We need the fully resolved type to detect aliased String types -}
                    rslvtypfull <- transType True rslviat
                    return $ not $ isString rslvtypfull
                  else return False
    return (if bang then makeReadOnlyIf ro nntyp else nntyp)
    where ub = if (isComposite typ) || (isFunPointer typ) then markUnbox else markBox
          
-- Pointer to void:
-- Translate to: CVoidPtr
-- If no Not-Null property: MayNull CVoidPtr
-- If Read-OnlyProperty: banged
transType _ iat@(_, (LCA.PtrType t _ _)) | isVoid t = do
    safe <- isNotNullItem iat
    ro <- isReadOnlyItem iat
    return $ makeReadOnlyIf ro $ addMayNullIfNot safe $ genType $ CS.TCon mapPtrVoid [] markBox
-- Derived pointer type for function type t:
-- Encode t, apply CFunPtr or CFunInc and make unboxed.
transType rslv iat@(_, (LCA.PtrType t _ _)) | isFunction t = do
    sub <- getRefSubItemAssoc iat
    enctyp <- encodeType rslv sub
    return $ genType $ CS.TCon ((mapFunDeriv $ isComplete t) ++ "_" ++ enctyp) [] markUnbox
-- Derived pointer type for array type t:
-- Translate t and use as result. Always boxed.
-- If no Not-Null property: apply MayNull
-- If Read-OnlyProperty: banged
transType rslv iat@(_, (LCA.PtrType t _ _)) | isArray t = do
    safe <- isNotNullItem iat
    ro <- isReadOnlyItem iat
    sub <- getRefSubItemAssoc iat
    typ <- transType rslv sub
    return $ makeReadOnlyIf ro $ addMayNullIfNot safe typ
-- Derived pointer type for (unsigned) char type:
-- If Read-Only property and not No-String property: translate to primitive type String
-- Otherwise translate to normal pointer (to U8).
transType rslv iat@(_, pt@(LCA.PtrType (LCA.DirectType (LCA.TyIntegral it) _ _) _ _)) | it == TyChar || it == TyUChar = do
    ro <- isReadOnlyItem iat
    ns <- isNoStringItem iat
    if ro && (not ns)
       then return $ genType $ CS.TCon "String" [] markBox
       else do
           safe <- isNotNullItem iat
           sub <- getRefSubItemAssoc iat
           typ <- transType rslv sub
           return $ makeReadOnlyIf ro $ addMayNullIfNot safe $ genType $ CS.TCon mapPtrDeriv [typ] markBox 
-- Derived pointer type for other type t:
-- Translate t. If unboxed and no function pointer make boxed, otherwise apply CPtr. Always boxed.
-- If no Not-Null property: apply MayNull
-- If Read-OnlyProperty: banged
transType rslv iat@(_, pt@(LCA.PtrType t _ _)) = do
    safe <- isNotNullItem iat
    ro <- isReadOnlyItem iat
    sub <- getRefSubItemAssoc iat
    typ <- transType rslv sub
    let rtyp = if (isUnboxed typ) && not (isFunPointer t) 
                then setBoxed typ
                else genType $ CS.TCon mapPtrDeriv [typ] markBox
    return $ makeReadOnlyIf ro $ addMayNullIfNot safe rtyp
-- Complete derived function type: ret (p1,..,pn)
-- Translate to: Cogent function type (p1,..,pn) -> ret, then apply properties.
transType rslv iat@(_, (LCA.FunctionType (LCA.FunType ret pars variadic) _)) = do
    sub <- getResultSubItemAssoc iat
    r <- transType rslv sub
    ps <- mapM (transParamType rslv iat) $ numberList pars
    let pt = mkParType (ps ++ if variadic then [variadicType] else [])
    applyProperties iat $ genType $ CS.TFun pt r
-- Incomplete derived function type: ret ()
-- Signal an error.
transType rslv iat@(iid, (LCA.FunctionType (LCA.FunTypeIncomplete ret) _)) =
    error ("Cannot translate incomplete function type for " ++ iid)
-- Derived array type for element type t:
-- Translate t, if again array type apply unbox operator, then apply generic array type. Always boxed.
-- If Read-OnlyProperty: banged
transType rslv iat@(_, (LCA.ArrayType t as _ _)) = do
    ro <- isReadOnlyItem iat
    sub <- getElemSubItemAssoc iat
    typ <- transType rslv sub
    return $ makeReadOnlyIf ro $ genType $ CS.TCon (mapArrDeriv as) [if isArray t then setUnboxed typ else typ] markBox 

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
-- If the typedef name has the Not-Null property, omit or remove MayNull step
-- otherwise move a MayNull step from the resolved type to the mapped name.
-- If the typedef name has the Read-Only property add readonly step.
encodeType rslv iat@(iid, (LCA.TypeDefType (LCA.TypeDefRef idnam typ _) _ _)) = do
    dt <- LCA.getDefTable
    srtn <- stopResolvTypeName idnam
    let rslvTypeName = (isExternTypeDef dt idnam) && not srtn
    safe <- isNotNullItem iat
    ro <- isReadOnlyItem iat
    let rslviat = (if not rslvTypeName then getTypedefItemAssoc idnam typ else (iid,typ))
    rslvtyp <- encodeType rslv rslviat
    tn <- mapNameToUpper idnam
    let nntyp = if rslv || rslvTypeName
                then rmMayNullStepIf safe rslvtyp
                else addMayNullStepIfNot (safe || (not $ hasMayNullStep rslvtyp)) (ustep ++ tn)
    bang <- if ro then do
        {- We need the fully resolved type to detect aliased String types -}
                    rslvtypfull <- transType True rslviat
                    return $ not $ isString rslvtypfull
                  else return False
    return (if bang then addReadOnlyStepIf ro nntyp else nntyp)
    where ustep = if isAggregate typ then mapUboxStep else ""
-- Derived pointer type for function type t:
-- Encode t, prepend pointer derivation step.
encodeType rslv iat@(_, (LCA.PtrType t _ _)) | isFunction t = do
    sub <- getRefSubItemAssoc iat
    tn <- encodeType rslv sub
    return (mapPtrStep ++ tn)
-- Derived pointer type for (unsigned) char type:
-- If Read-Only property and not No-String property: encode as "String"
-- Otherwise encode as normal pointer (to U8).
encodeType rslv iat@(_, pt@(LCA.PtrType (LCA.DirectType (LCA.TyIntegral it) _ _) _ _)) | it == TyChar || it == TyUChar = do
    ro <- isReadOnlyItem iat
    ns <- isNoStringItem iat
    if ro && (not ns)
       then return "String"
       else do
           safe <- isNotNullItem iat
           sub <- getRefSubItemAssoc iat
           tn <- encodeType rslv sub
           return $ addReadOnlyStepIf ro $ addMayNullStepIfNot safe (mapPtrStep ++ tn)
-- Derived pointer type for other type t:
-- Encode t, for aggregate type remove unbox step, otherwise prepend pointer derivation step.
-- If no Not-Null property, add MayNull step.
-- If Read-Only property  add readonly step.
encodeType rslv iat@(_, pt@(LCA.PtrType t _ _)) = do
    safe <- isNotNullItem iat
    ro <- isReadOnlyItem iat
    sub <- getRefSubItemAssoc iat
    tn <- encodeType rslv sub
    let htn = if isAggregate t then (rmUboxStep tn) else (mapPtrStep ++ tn)
    return $ addReadOnlyStepIf ro $ addMayNullStepIfNot safe htn
-- Complete derived function type: ret (p1,..,pn)
-- Encode ret, prepend function derivation step using encoded pi.
encodeType rslv iat@(_, (LCA.FunctionType (LCA.FunType ret pars variadic) _)) = do
    sub <- getResultSubItemAssoc iat
    tn <- encodeType rslv sub
    encpars <- mapM (encodeParamType rslv iat) $ numberList pars
    let vencpars = if variadic then encpars ++ [mapRoStep ++ variadicTypeName] else encpars
    arProps <- getAddResultProperties iat
    let varProps = if variadic then arProps ++ [False] else arProps
    let ps = map (\(arProp,s) -> if arProp then mapModStep ++ s else s) $ zip varProps vencpars
    return ((mapFunStep ps) ++ tn)
-- Incomplete derived function type: ret ()
-- Encode ret, prepend incomplete function derivation step.
encodeType rslv iat@(_, (LCA.FunctionType (LCA.FunTypeIncomplete ret) _)) = do
    sub <- getResultSubItemAssoc iat
    tn <- encodeType rslv sub
    return (mapIncFunStep ++ tn)
-- Derived array type for element type t:
-- Encode t, prepend array derivation step and unbox step.
-- If Read-Only property add readonly step.
encodeType rslv iat@(_, (LCA.ArrayType t as _ _)) = do
    ro <- isReadOnlyItem iat
    sub <- getElemSubItemAssoc iat
    tn <- encodeType rslv sub
    return $ addReadOnlyStepIf ro (mapUboxStep ++ (mapArrStep as) ++ tn)

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
rmMayNullIf True t = rmMayNullThroughBang t
rmMayNullIf False t = t

addMayNullIfNot :: Bool -> GenType -> GenType
addMayNullIfNot False (GenType (CS.TBang t) o) = (GenType (CS.TBang $ addMayNullIfNot False t) o)
addMayNullIfNot False t | hasMayNull t = t
addMayNullIfNot False t = genType $ CS.TCon mapMayNull [t] markBox
addMayNullIfNot True t = t

rmMayNullStepIf :: Bool -> String -> String
rmMayNullStepIf True t = rmMayNullStepThroughRo t
rmMayNullStepIf False t = t
    
addMayNullStepIfNot :: Bool -> String -> String
addMayNullStepIfNot False t = addMayNullStep t
addMayNullStepIfNot True t = t

rmMayNullThroughBang :: GenType -> GenType
rmMayNullThroughBang (GenType (CS.TBang (GenType (CS.TCon tn [t] _) _)) o) | tn == mapMayNull = GenType (CS.TBang t) o
rmMayNullThroughBang (GenType (CS.TCon tn [t] _) _) | tn == mapMayNull = t
rmMayNullThroughBang t = t

hasMayNull :: GenType -> Bool
hasMayNull (GenType (CS.TBang t) _) = hasMayNull t
hasMayNull (GenType (CS.TCon tn _ _) _) | tn == mapMayNull = True
hasMayNull _ = False

hasMayNullStep :: String -> Bool
hasMayNullStep t = (mapMayNullStep `isPrefixOf` t) || ((mapRoStep ++ mapMayNullStep) `isPrefixOf` t)

makeReadOnlyIf :: Bool -> GenType -> GenType
makeReadOnlyIf True t@(GenType (CS.TBang _) _) = t
makeReadOnlyIf True t = genType $ CS.TBang t
makeReadOnlyIf False t = t

addReadOnlyStepIf :: Bool -> String -> String
addReadOnlyStepIf True t@('R' : '_' : _) = t
addReadOnlyStepIf True t = mapRoStep ++ t
addReadOnlyStepIf False t = t

rmReadOnly :: GenType -> GenType
rmReadOnly (GenType (CS.TBang t) _) = t
rmReadOnly t = t

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

-- | Apply item properties to a mapped function type.
-- The first parameter is the item associated type of the function.
-- First add all parameters with a Global-State property.
-- Then for every parameter which has the Add-Result or Global-State property and no Read-Only property
-- its type is appended to the result type.
-- Then if the function has a Heap-Use property, the Heap type is appended to the parameters 
-- and the result type.
-- Comment markers are removed from these types to avoid duplication of comments.
applyProperties :: ItemAssocType -> GenType -> FTrav GenType
applyProperties iat (GenType (CS.TFun pt rt) o) = do
    arProps <- getAddResultProperties iat
    let artypes = map snd $ filter fst $ zip arProps ptl
    gspars <- makeGlobalStateParams iat
    gstypes <- mapM makeGlobalStateType $ map (snd . fst) gspars
    gsartypes <- mapM makeGlobalStateType $ map (snd . fst) $ filter snd gspars
    huProp <- isHeapUseItem iat
    let hutype = if huProp then [makeHeapType] else []
    let allpartypes = ptl ++ gstypes ++ hutype
    let arpartypes = artypes ++ gsartypes ++ hutype
    return $ GenType (CS.TFun (mkParType allpartypes) (mkParType $ addPars rt $ map remComment $ arpartypes)) o 
    where addPars (GenType CS.TUnit _) ps = ps
          addPars r ps = r : ps
          ptl = ptlist pt
          ptlist (GenType CS.TUnit _) = []
          ptlist (GenType (CS.TTuple ts) _) = ts
          ptlist gt = [gt]

shallAddResultGS :: GenType -> Bool
shallAddResultGS t = not $ isReadOnly t

-- | Determine the Cogent type from the item associated type of a global state parameter
-- The type is ignored, the Cogent type is determined from the Global-State property only.
makeGlobalStateType :: ItemAssocType -> FTrav GenType
makeGlobalStateType iat@(iid,_) = do
    ro <- isReadOnlyItem iat
    gs <- getGlobalStateProperty iid
    return $ makeReadOnlyIf ro $ genType $ CS.TCon (globStateType gs) [] $ markBox

makeHeapType :: GenType
makeHeapType = genType $ CS.TCon heapType [] markBox

mkBoxedType :: String -> Origin -> GenType
mkBoxedType nam = GenType (CS.TCon nam [] $ markBox)

mkUnboxedType :: String -> Origin -> GenType
mkUnboxedType nam = GenType (CS.TCon nam [] $ markUnbox)

-- | Convert an arbitrary Cogent type T to the function type () -> T
mkFunType :: GenType -> GenType
mkFunType t = genType $ CS.TFun (mkParType []) t

variadicType = makeReadOnlyIf True $ genType (CS.TCon variadicTypeName [] markBox)
variadicTypeName = "VariadicCogentParameters"

-- | Translate a C parameter declaration to the adjusted Cogent parameter type.
-- The parameter declaration is specified together with the parameter position.
-- The first argument specifies whether typedef names shall be resolved.
-- The second argument is the function's ItemAssocType.
transParamType :: Bool -> ItemAssocType -> (Int,LCA.ParamDecl) -> FTrav GenType
transParamType rslv iat ipd@(_,pd) = do
    t <- transType rslv $ getParamSubItemAssoc iat ipd
    return $ GenType (typeOfGT t) $ origin pd

-- | Encode a type as parameter type.
-- The parameter declaration is specified together with the parameter position.
-- For an array type: adjust by removing unbox step.
-- For a function type: adjust by adding pointer step.
encodeParamType :: Bool -> ItemAssocType -> (Int,LCA.ParamDecl) -> FTrav String
encodeParamType rslv iat ipd@(_,pd) = do
    typ <- encodeType rslv $ getParamSubItemAssoc iat ipd
    if isArray $ LCA.declType pd
       then return $ rmUboxStep typ
       else return typ

arraySizeType :: LCA.ArraySize -> GenType
arraySizeType (LCA.ArraySize _ (LCS.CConst (LCS.CIntConst ci _))) =
    genType $ CS.TCon tnam [] markBox
    where tnam = if i < 257 then "U8" else if i < 65537 then "U16" else "U32"
          i = LC.getCInteger ci
arraySizeType _ = genType $ CS.TCon "U32" [] markBox

{- Translating function bodies -}
{- --------------------------- -}

-- | Retrieve the C type of a C expression.
-- This function is only used for CConst, CUnary, CBinary, CVar expressions.
-- The StmtCtx is only used for CStatExpr which are not processed by Gencot, therefore we always use LoopCtx as a dummy.
-- The ExprSide for CConst, CUnary, CBinary must be RValue, for CVar it is ignored.
exprType :: LC.CExpr -> FTrav LCA.Type
exprType e = LCA.tExpr LoopCtx RValue e

transBody :: ItemAssocType -> LC.CStat -> [LCA.ParamDecl] -> FTrav GenExpr
transBody fiat s pars = do
    resetVarCounters
    tconf <- getTConf
    b <- bindStat s
    riat <- getResultSubItemAssoc fiat
    let r = if isVoid $ snd riat then mkUnitExpr else mkVarExpr resVar
    e <- extendExpr fiat r pars
    return $ cleanSrc $ postproc tconf $ mkBodyExpr b e

transExpr :: LC.CExpr -> FTrav GenExpr
transExpr e = do
    tconf <- getTConf
    bp <- bindExpr e
    return $ cleanSrc $ postproc tconf $ mkPlainExpr bp

bindStat :: LC.CStat -> FTrav GenBnd
bindStat s@(LC.CExpr Nothing _) =
    insertStatSrc s mkNullBinding
bindStat s@(LC.CExpr (Just e) _) = do
    resetValCounter
    bpe <- bindExpr e
    insertStatSrc s $ mkExpBinding bpe
bindStat s@(LC.CReturn Nothing _) =
    insertStatSrc s $ mkRetBinding $ mkUnitBindsPair 0
bindStat s@(LC.CReturn (Just e) _) = do
    resetValCounter
    bpe <- bindExpr e
    insertStatSrc s $ mkRetBinding bpe
bindStat s@(LC.CBreak _) =
    insertStatSrc s $ mkBreakBinding
bindStat s@(LC.CCont _) =
    insertStatSrc s $ mkContBinding
bindStat s@(LC.CCompound lbls bis _) = do
    LCA.enterBlockScope
    enterItemScope
    res <- if not $ null lbls
              then insertStatSrc s $ mkDummyBinding "Local labels not supported in compound statement"
              else bindBlockItems bis
    leaveItemScope
    LCA.leaveBlockScope
    return res
bindStat s@(LC.CIf e s1 Nothing _) = do
    resetValCounter
    bpe <- bindExpr e
    bs1 <- bindStat s1
    let bs2 = mkNullBinding
    insertStatSrc s $ mkIfBinding bpe bs1 bs2
bindStat s@(LC.CIf e s1 (Just s2) _) = do
    resetValCounter
    bpe <- bindExpr e
    bs1 <- bindStat s1
    bs2 <- bindStat s2
    insertStatSrc s $ mkIfBinding bpe bs1 bs2
bindStat s@(LC.CSwitch e s1 _) = do
    resetValCounter
    bpe <- bindExpr e
    lbls <- getLabels s1
    bs <- bindSwitchBody s1 (length lbls)
    insertStatSrc s $ mkSwitchBinding bpe lbls bs
    where getLabels (LC.CCompound _ bis _) = bindSwitchLabels bis
          getLabels _ = return []
bindStat s@(LC.CCase _ _ _) =
    insertStatSrc s $ mkDummyBinding "Case statement only supported in direct switch body"
bindStat s@(LC.CDefault _ _) =
    insertStatSrc s $ mkDummyBinding "Default statement only supported in direct switch body"
bindStat s@(LC.CFor c1 me2 me3 s1 _) = do
    case checkForTrans s of
         Left reason -> insertStatSrc s $ mkDummyBinding ("Unsupported form of for loop: " ++ reason)
         Right exprmax -> do
             LCA.enterBlockScope
             enterItemScope
             resetValCounter
             bpm <- bindExpr exprmax
             bc1 <- case c1 of
                         Left (Just e1) -> do
                             bp1 <- bindExpr e1
                             return (Left (Just bp1))
                         Left Nothing -> return (Left Nothing)
                         Right d -> do
                             dbpl <- bindForDecl d
                             return (Right dbpl)
             b1 <- bindStat s1
             bp2 <- bindExpr $ fromJust me2
             bp3 <- bindExpr $ fromJust me3
             res <- insertStatSrc s $ mkForBinding bpm bc1 bp2 bp3 b1
             leaveItemScope
             LCA.leaveBlockScope
             return res
bindStat s = 
    insertStatSrc s $ mkDummyBinding "Translation of statement not yet implemented"

bindSwitchBody :: LC.CStat -> Int -> FTrav GenBnd
bindSwitchBody s@(LC.CCompound [] bis _) _ | any isDecl bis = 
    insertStatSrc s $ mkDummyBinding "Declarations not supported in switch body"
    where isDecl (LC.CBlockDecl _) = True
          isDecl _ = False
bindSwitchBody s@(LC.CCompound [] bis _) grps = do
    -- we do not need LCA.enterBlockScope because there are no declarations (?)
    bindSwitchItems bis 1 grps False
bindSwitchBody s _ = insertStatSrc s $ mkDummyBinding "Unsupported switch body"

bindSwitchLabels :: [LC.CBlockItem] -> FTrav [Maybe BindsPair]
bindSwitchLabels [] = return []
bindSwitchLabels ((LC.CBlockStmt (LC.CCase e _ _)) : bis) = do
    resetValCounter
    bpe <- bindExpr e
    bs <- bindSwitchLabels bis
    return ((Just bpe) : bs)
bindSwitchLabels ((LC.CBlockStmt (LC.CDefault _ _)) : bis) = do
    bs <- bindSwitchLabels bis
    return (Nothing : bs) 
bindSwitchLabels (_ : bis) = bindSwitchLabels bis

isLbld :: LC.CBlockItem -> Bool
isLbld (LC.CBlockStmt (LC.CCase _ _ _)) = True
isLbld (LC.CBlockStmt (LC.CDefault _ _)) = True
isLbld _ = False

-- | Process list of statements in a switch body.
-- nr is the group number for the first statement group, grps is the total number of groups in the switch body
-- dfltSeen is true if a default statement has already been processed.
bindSwitchItems :: [LC.CBlockItem] -> Int -> Int -> Bool -> FTrav GenBnd
bindSwitchItems [] _ _ _ = return mkNullBinding
bindSwitchItems bis@(s : bis1) nr grps dfltSeen | not (isLbld s) = bindSwitchItems bis1 nr grps dfltSeen
bindSwitchItems bis@((LC.CBlockStmt s) : bis1) nr grps dfltSeen = do
    b1 <- bindSwitchGroup s ss1 nr grps dfltSeen'
    b2 <- bindSwitchItems ss2 (1+nr) grps dfltSeen'
    insertBlockItemsSrc bis $ mkSeqBinding b1 b2
    where (ss1,ss2) = break isLbld bis1
          dfltSeen' = if dfltSeen then True else isDflt s
          isDflt (LC.CDefault _ _) = True
          isDflt _ = False

bindSwitchGroup :: LC.CStat -> [LC.CBlockItem] -> Int -> Int -> Bool -> FTrav GenBnd
bindSwitchGroup s bis nr grps dfltSeen = do
    b <- bindBlockItems (LC.CBlockStmt s' : bis)
    return $ mkCaseBinding b nr grps dfltSeen
    where s' = case s of
                  LC.CDefault s' _ -> s'
                  LC.CCase _ s' _  -> s'

bindBlockItems :: [LC.CBlockItem] -> FTrav GenBnd
bindBlockItems [] = return mkNullBinding
bindBlockItems [(LC.CBlockStmt s)] = bindStat s
bindBlockItems bis@((LC.CBlockStmt s) : bis1) = do
    b <- bindStat s
    bs <- bindBlockItems bis1
    insertBlockItemsSrc bis $ mkSeqBinding b bs
bindBlockItems ((LC.CBlockDecl d) : bis) =
    bindDecl d bis

type DeclElem = (Maybe LC.CDeclr, Maybe LC.CInit, Maybe LC.CExpr)
type ProcDeclSpecs = ([LC.CStorageSpec], [LC.CAttr], [LC.CTypeQual], LCA.TypeSpecAnalysis, [LC.CFunSpec])

processDeclSpecs :: [LC.CDeclSpec] -> FTrav ProcDeclSpecs
processDeclSpecs specs = do
    let (sspecs, attrs, tquals, tspecs, fspecs, _) = LCA.partitionDeclSpecs specs
    ctspecs <- LCA.canonicalTypeSpec tspecs
    return (sspecs, attrs, tquals, ctspecs, fspecs)
    
-- | Processing a declaration together with the following block content.
bindDecl :: LC.CDecl -> [LC.CBlockItem] -> FTrav GenBnd
bindDecl dc@(LC.CDecl specs dcs _) bis = do
    pspecs <- processDeclSpecs specs
    bindDeclrs pspecs dcs bis
bindDecl sa@(LC.CStaticAssert _ _ _) bis = 
    insertBlockItemsSrc ((LC.CBlockDecl sa) : bis) $ mkDummyBinding "Static assertions not supported"

-- | Standalone processing of a declaration in a for loop
-- The main difference is the handling of the source.
bindForDecl :: LC.CDecl -> FTrav [(TypedVar,BindsPair)]
bindForDecl dc@(LC.CDecl specs dcs _) = do
    pspecs <- processDeclSpecs specs
    mapM (uncurry bindDeclr) (zip (repeat pspecs) dcs)
bindForDecl sa@(LC.CStaticAssert _ _ _) = return []

-- | We treat a declaration with a sequence of declarators as a sequence of declarations with a single declarator and replicate the specifiers
bindDeclrs :: ProcDeclSpecs -> [DeclElem] -> [LC.CBlockItem] -> FTrav GenBnd
bindDeclrs _ [] bis = bindBlockItems bis
bindDeclrs pspecs (dc : dcs) bis = do
    (v,bp) <- bindDeclr pspecs dc
    bs <- bindDeclrs pspecs dcs bis
    insertBlockItemsSrc ((LC.CBlockDecl d) : bis) $ mkDecBinding v bp bs

bindDeclr :: ProcDeclSpecs -> DeclElem -> FTrav (TypedVar,BindsPair)
bindDeclr (ss,a,tq,tsa,fs) (Just declr@(LC.CDeclr (Just nam) _ _ _ _),mi,me) = do
    v <- transObjName nam
    vardeclInfo@(VarDeclInfo _ _ _ _ typ _) <-
        LCA.analyseVarDecl False ss a tq tsa fs declr [] Nothing

    num <- nextVarNum s  -- not yet used
    -- bindDeclr is only used for local declarations, therefore the function context is defined
    (Just fdef) <- getFunDef
    sfn <- getFileName
    let fid = getIndividualItemId fdef sfn -- not yet used
        vid = (localItemId s) -- here num and fid must be used when local item ids are changed.

    t <- transType True (vid,typ)

    _ <- maybe (return Nothing) (liftM Just . tInit typ) mi
    bp <- bindInit mi t

    -- this inserts the new variable into the symbol table, hence it must be done after processing mi by bindInit
    LCA.localVarDecl vardeclInfo mi
    
    registerItemId s vid
    return ((v,t),bp)
    where s = LCI.identToString nam
bindDeclr _ _ = return (("",unitType),mkEmptyBindsPair)

bindInit :: Maybe LC.CInit -> GenType -> FTrav BindsPair
bindInit Nothing t = do
    cnt <- getValCounter
    return $ mkDefaultBindsPair cnt t
bindInit (Just (LC.CInitExpr e _)) _ = bindExpr e
bindInit (Just (LC.CInitList il _)) _ = do
    cnt <- getValCounter
    return $ mkDummyBindsPair cnt "Non-scalar initializers not yet implemented"

bindExpr :: LC.CExpr -> FTrav BindsPair
bindExpr e@(LC.CConst (LC.CIntConst i _)) = do
    cnt <- getValCounter
    ct <- exprType e
    t <- transType True ("",ct)
    insertExprSrc e $ mkIntLitBindsPair cnt t $ LC.getCInteger i
bindExpr e@(LC.CConst (LC.CCharConst c _)) = do
    cnt <- getValCounter
    insertExprSrc e $ 
        if length ch == 1 
           then mkCharLitBindsPair cnt $ head ch
           else mkDummyBindsPair cnt "Multi character constants not supported"
    where ch = LC.getCChar c
bindExpr e@(LC.CConst (LC.CFloatConst _ _)) = do
    cnt <- getValCounter
    insertExprSrc e $ mkDummyBindsPair cnt "Float literals not supported"
bindExpr e@(LC.CConst (LC.CStrConst s _)) = do
    cnt <- getValCounter
    insertExprSrc e $ mkStringLitBindsPair cnt $ LC.getCString s
bindExpr e@(LC.CVar nam _) = do
    v <- transObjName nam
    cnt <- getValCounter
    ct <- exprType e
    iid <- getObjectItemId nam
    t <- transType True (iid,ct)
    insertExprSrc e $ mkValVarBindsPair cnt (v,t)
bindExpr e@(LC.CMember e1 nam arrow _) = do
    bp1 <- bindExpr e1
    m <- mapIfUpper nam
    cnt <- getCmpCounter
    insertExprSrc e $ mkMemBindsPair cnt m bp1
bindExpr e@(LC.CIndex e1 e2 _) = do
    bp1 <- bindExpr e1
    bp2 <- bindExpr e2
    cnt <- getCmpCounter
    insertExprSrc e $ mkIdxBindsPair cnt bp1 bp2
bindExpr e@(LC.CUnary LC.CNegOp e1 _) = do
    -- not i -> if i==0 then 1 else 0
    bp1 <- bindExpr e1
    let t1 = snd (leadVar bp1)
    cnt <- getValCounter
    let c0 = mkIntLitBindsPair cnt t1 0
    cnt <- getValCounter
    let c1 = mkIntLitBindsPair cnt t1 1
    insertExprSrc e $ mkIfBindsPair (mkOpBindsPair mkBoolType "==" [bp1,c0]) c1 c0
bindExpr e@(LC.CUnary LC.CIndOp e1 _) = do
    bp1 <- bindExpr e1
    cnt <- getCmpCounter
    insertExprSrc e $ mkMemBindsPair cnt "cont" bp1
bindExpr e@(LC.CUnary op e1 _) | elem op [LC.CPlusOp,LC.CMinOp,LC.CCompOp] = do
    bp1 <- bindExpr e1
    ct1 <- exprType e1
    t1 <- transType True ("",ct1)
    insertExprSrc e $ mkOpBindsPair t1 (transUnOp op) [bp1]
bindExpr e@(LC.CUnary op e1 _) | elem op [LC.CPreIncOp,LC.CPreDecOp,LC.CPostIncOp,LC.CPostDecOp] = do
    bp1 <- bindExpr e1
    ct1 <- exprType e1
    t1 <- transType True ("",ct1)
    cnt <- getValCounter
    let bp2 = mkIntLitBindsPair cnt t1 1
    ct <- exprType e
    t <- transType True ("",ct)
    insertExprSrc e $ mkAssBindsPair post t (transUnOp op) bp1 bp2
    where post = elem op [LC.CPostIncOp,LC.CPostDecOp]
bindExpr e@(LC.CBinary LC.CLndOp e1 e2 _) = do
    -- e1 && e2 -> if e1 then e2 else 0
    bp1 <- bindExpr e1
    bp2 <- bindExpr e2
    ct2 <- exprType e2
    t2 <- transType True ("",ct2)
    cnt <- getValCounter
    let c0 = mkIntLitBindsPair cnt t2 0
    insertExprSrc e $ mkIfBindsPair bp1 bp2 c0
bindExpr e@(LC.CBinary LC.CLorOp e1 e2 _) = do
    -- e1 || e2 -> if e1 then 1 else e2
    bp1 <- bindExpr e1
    bp2 <- bindExpr e2
    ct2 <- exprType e2
    t2 <- transType True ("",ct2)
    cnt <- getValCounter
    let c1 = mkIntLitBindsPair cnt t2 1
    insertExprSrc e $ mkIfBindsPair bp1 c1 bp2
bindExpr e@(LC.CBinary op e1 e2 _) = do
    bp1 <- bindExpr e1
    bp2 <- bindExpr e2
    ct <- exprType e
    t <- transType True ("",ct)
    insertExprSrc e $ mkOpBindsPair t (transBinOp op) [bp1,bp2]
bindExpr e@(LC.CCall fv@(LC.CVar nam _) es _) = do
    bps <- mapM bindExpr es
    f <- transObjName nam
    ctf <- exprType fv
    iid <- getObjectItemId nam
    t <- transType True (iid,ctf)
    (vdres,arprops,gshupars,_) <- getFunctionProperties nam
    let invalpars = filter (null . fst . fst) gshupars
    cnt <- if (null bps && not vdres) || (not $ null invalpars) then getValCounter else return 0 
    let rvar = if vdres then "" else if null bps then valVar cnt else leadVar (head bps)
    let vs = (map leadVar bps) ++ (map (fst . fst) gshupars)
    insertExprSrc e $
        if null invalpars
           then mkAppBindsPair (f,t) bps rvar vs arprops $ map fst gshupars
           else mkDummyBindsPair cnt ("No value available for property " ++ (snd (head invalpars)))
bindExpr e@(LC.CCall _ _ _) = do
    cnt <- getValCounter
    insertExprSrc e $ mkDummyBindsPair cnt "Translation of function expression not yet implemented"
bindExpr e@(LC.CAssign op e1 e2 _) = do
    bp1 <- bindExpr e1
    bp2 <- bindExpr e2
    insertExprSrc e $ mkAssBindsPair False unitType (transAssOp op) bp1 bp2
bindExpr e@(LC.CCond e1 (Just e2) e3 _) = do
    bp1 <- bindExpr e1
    bp2 <- bindExpr e2
    bp3 <- bindExpr e3
    insertExprSrc e $ mkIfBindsPair bp1 bp2 bp3
bindExpr e@(LC.CComma es _) = do
    bps <- mapM bindExpr es
    insertExprSrc e $ concatBindsPairs bps
bindExpr e = do
    cnt <- getValCounter
    insertExprSrc e $ mkDummyBindsPair cnt "Translation of expression not yet implemented"

-- | Add a statement source to a binding
insertStatSrc :: LC.CStat -> GenBnd -> FTrav GenBnd
insertStatSrc src (CS.Binding ip t (GenExpr e o _) v) = do
    src' <- C.transStat src
    return $ (CS.Binding ip t (GenExpr e o (Just src')) v)

-- | Add an expression source to the final binding in the main list
-- The expression is inserted as an expression statement.
insertExprSrc :: LC.CExpr -> BindsPair -> FTrav BindsPair
insertExprSrc src (main,putback) = do
    src' <- C.transExpr src
    let srcstat = (LQ.Exp (Just src') noOrigin)
    return $ ((CS.Binding ip t (GenExpr e o (Just srcstat)) v) : tail main,putback)
    where (CS.Binding ip t (GenExpr e o _) v) = head main

-- | Add a block item sequence source to a binding
-- The sequence is inserted as a compound statement
insertBlockItemsSrc :: [LC.CBlockItem] -> GenBnd -> FTrav GenBnd
insertBlockItemsSrc src b = insertStatSrc (LC.CCompound [] src LCN.undefNode) b

-- | Description of a single parameter: name, type, properties.
-- A parameter caused by a hu property of the function is additionally marked by an own hu property.
-- Note that if a function parameter has a hu property it is associated with the dereferenced parameter instead.
data ParamDesc = ParamDesc {
    nameOfParamDesc :: CCS.VarName, 
    typeOfParamDesc :: GenType, 
    propOfParamDesc :: [String]}

-- | Description of a function: name, type, properties, parameter descriptions.
-- The type already includes the effect of ModificationFunction properties,
-- the parameter descriptions describe the C and virtual parameters in their original order.
data FuncDesc = FuncDesc {
    nameOfFuncDesc :: CCS.FunName, 
    typeOfFuncDesc :: GenType, 
    propOfFuncDesc :: [String], 
    parsOfFuncDesc :: [ParamDesc]}

-- | Construct a function description from the function declaration.
getFuncDesc :: LCA.VarDecl -> FTrav FuncDesc
getFuncDesc decl = do
    name <- mapIfUpper $ LCA.declIdent decl
    iid <- getObjectItemId $ LCA.declIdent decl
    let iat = (iid, LCA.declType decl)
    typ <- transType True iat
    props <- getItemProperties iat
    parms <- getAllParamDesc iat
    return $ FuncDesc name typ props parms

-- | Construct the descriptions for all parameters of a function
-- The parameter types are not taken from the translated function type, because
-- there they may have been rearranged by processing a ModificationFunction property.
getAllParamDesc :: ItemAssocType -> FTrav [ParamDesc]
getAllParamDesc iat@(iid,(LCA.FunctionType (LCA.FunType _ pds isVar) _)) = do
    pns <- mapM mapIfUpper $ map LCA.declIdent pds
    pts <- mapM (transType True) piats
    pps <- mapM getItemProperties piats
    let nonvirt = map (\(n,t,p) -> ParamDesc n t p) $ zip3 pns pts pps
    gsps <- getGlobalStateSubItemIds iat -- the item ids of all gs parameters
    gsprops <- mapM getGlobalStateProperty $ map fst gsps -- the gs properties of all gs parameters
    gsvars <- mapM getGlobalStateId gsprops -- the global var item ids or "" for all gs parameters
    gsvirtnosort <- mapM makeGlobalStateParamDesc $ zip gsps gsprops -- the descriptions for all gs parameters
    let gsvirt = map snd $ sortOn fst $ zip gsprops gsvirtnosort
    huprop <- isHeapUseItem iat
    let huvirt = if huprop then [makeHeapUseParamDesc $ map nameOfParamDesc (nonvirt ++ gsvirt)] else []
    let variadic = if isVar then [makeVariadicParamDesc] else []
    return (nonvirt ++ gsvirt ++ huvirt ++ variadic)
    where piats = map (getParamSubItemAssoc iat) $ numberList pds

-- | Construct the parameter description for a GlobalState parameter.
-- The first string is the item id od the parameter.
-- The boolean is true if it has no ReadOnly property.
-- The second string is the GlobalState property.
makeGlobalStateParamDesc :: ((String, Bool), String) -> FTrav ParamDesc
makeGlobalStateParamDesc ((iid,noro), gs) = do
    name <- mapIfUpper $ LCI.Ident (getParamName iid) 0 LCN.undefNode
    gsvar <- getGlobalStateId gs -- global var item id or ""
    if null gsvar
       then -- global variable not available, use type synonym
         let typ = makeReadOnlyIf (not noro) $ genType $ CS.TCon (globStateType gs) [] $ markBox
         props <- getProperties iid
         return $ ParamDesc name typ props
       else -- global variable found, use its type
         mdec <- LCA.lookupObject $ LCI.Ident (getObjFunName gsvar) 0 LCN.undefNode
         case mdec of
              Nothing -> return $ ParamDesc "" unitType []
              Just decl -> do
                  let piat = (iid,LCA.PtrType (LCA.declType decl) LCA.noTypeQuals LCA.noAttributes)
                  typ <- transType True piat
                  props <- getItemProperties piat
                  return $ ParamDesc name typ props

-- | construct the parameter description for the HeapUse parameter.
-- The argument is the list of names of all other parameters.
-- The parameter is marked by an artificial hu property. 
makeHeapUseParamDesc :: [CCS.VarName] -> ParamDesc
makeHeapUseParamDesc pnams = 
    ParamDesc (heapParamName pnams) makeHeapType ["hu"]

-- | construct the parameter description for the variadic parameter.
makeVariadicParamDesc :: ParamDesc
makeVariadicParamDesc = 
    ParamDesc variadicParamName variadicType []

-- | Return the variadic parameter description, if present.
getVariadicParamDesc :: FuncDesc -> Maybe ParamDesc
getVariadicParamDesc fdes = 
    if nameOfParamDesc pdes == variadicParamName then Just pdes else Nothing
    where pdes = last $ parsOfFuncDesc fdes

-- | Return the function result type
getResultType :: FuncDesc -> GenType
getResultType fdes = 
    case typeOfGT $ typeOfFuncDesc fdes of
         CS.TFun _ t -> t
    
-- | Return the HeapUse parameter description, if present.
-- That is the first parameter marked by an hu property.
getHeapUseParamDesc :: FuncDesc -> Maybe ParamDesc
getHeapUseParamDesc fdes =
    find (\pdes -> elem "hu" $ propOfParamDesc pdes) $ parsOfFuncDesc fdes

-- | Return the sequence of GlobalState properties from the parameter descriptions.
getGlobalStateParamProps :: FuncDesc -> [String]
getGlobalStateParamProps fdes = 
    filter (not . null) $ map getGSProp $ parsOfFuncDesc fdes
    where getGSProp = (fromMaybe "") . (find (\p -> "gs" `isPrefixOf` p)) . propOfParamDesc

-- | Search a parameter description for a HeapUse parameter.
-- If not found return a description with empty name, unit type, and only the HeapUse property.
searchHeapUseParamDesc :: FuncDesc -> ParamDesc
searchHeapUseParamDesc fdes =
    case getHeapUseParamDesc fdes of
         Nothing -> ParamDesc "" unitType ["hu"]
         Just pdes -> pdes

-- | Search a parameter description with a specific GlobalState property.
-- If not found return a description with empty name, unit type, and only the GlobalState property.
searchGlobalStateParamDesc :: FuncDesc -> String -> ParamDesc
searchGlobalStateParamDesc fdes gsprop =
    case find (\pdes -> elem gsprop $ propOfParamDesc pdes) $ parsOfFuncDesc fdes of
         Nothing -> ParamDesc "" unitType [gsprop]
         Just pdes -> pdes

isAddResultParam :: ParamDesc -> Bool
isAddResultParam pdes =
    ((elem "ar" props) && (not $ elem "ro" props)) ||
    (any (\p -> "gs" `isPrefixOf` p) props) ||
    (elem "hu" props)
    where props = propOfParamDesc pdes

getTypedVarFromParamDesc :: ParamDesc -> TypedVar
getTypedVarFromParamDesc pdes = (nameOfParamDesc pdes, typeOfParamDesc pdes)

-- | Retrieve the actual virtual parameters for a function call from the context.
-- The argument is the description of the invoked function.
-- The result is a sequence of parameter descriptions of the surrounding function,
-- ordered according to the use in the invoked function.
-- If a virtual parameter is not available, the resulting parameter description has 
-- an empty name, a unit type and (only) the required property.
getVirtParamsFromContext :: FuncDesc -> FTrav [ParamDesc]
getVirtParamsFromContext fdes = do
    mfdef <- getFunDef
    case mfdef of
         Nothing -> return []
         Just (LCA.FunctionDef (LCA.FunDef decl _ _)) -> do
             ctxfdes <- getFuncDesc decl
             let gspdes = map (searchGlobalStateParamDesc ctxfdes) $ getGlobalStateParamProps fdes
             let hupdes = if elem "hu" $ propOfFuncDesc fdes
                             then [searchHeapUseParamDesc ctxfdes]
                             else []
             let vrpdes = case getVariadicParamDesc fdes of
                             Nothing -> []
                             Just pdes -> [pdes]
             return (gspdes ++ hupdes ++ vrpdes)

-- | Get a variable for binding the result of a function.
-- The first argument is the function result type.
-- The second argument is the list of all parameter BindsPairs.
-- If the result type is the unit type (C function has result type void), return a wildcard.
-- Otherwise reuse the value variable of the first parameter, or return a new value variable if there are no parameters.
getResultVar :: GenType -> [BindsPair] -> FTrav TypedVar
getResultVar rt bps = do
    rv <- if null bps 
             then do
                    cnt <- getValCounter
                    return (valVar cnt,rt)
             else return (fst $ leadVar $ head bps, rt)
    return (if rt == unitType then ("_",rt) else rv)

-- | Determine lists of actual parameters and patterns to bind the result of a function call.
-- The first argument is the description of the invoked function.
-- The second argument is the list of translated C argument expressions.
processParamVals :: FuncDesc -> [BindsPair] -> FTrav ([BindsPair], [GenIrrefPatn])
processParamVals fdes pvals = do
    -- construct BindsPairs for all virtual parameters
    vpds <- getVirtParamsFromContext fdes
    vpbps <- mapM (\pdes -> do 
                             cnt <- getValCounter
                             return $ mkValVarBindsPair cnt $ getTypedVarFromParamDesc pdes) vpds
    let -- modify types of non-virtual parameters
        nvpbps = map (\(bp, pdes) -> replaceBoundVarType (typeOfParamDesc pdes) bp) $ zip pvals pdess
        -- the list of all actual parameters
        allpbps = nvpbps ++ vpbps
        -- actual parameters paired with mf flags
        mfpbps = zip allpbps $ map hasMf pdess
    -- provide value variable index if there is a single parameter and it has an mf flag
    cnt <- if length mfpbps == 1 && snd (head mfpbps) then getValCounter else return 0
    -- additional result variables
    let arvars = map (\(bp,pdes) -> (lvalVar bp, hasMf pdes) $ filter (\(_,pdes) -> isAddResultParam pdes) $ zip allpbps pdess
    -- variable for original function result
    rvar <- getResultVar rt allpbps
    -- the list of all result variables, paired with mf flags
    -- the original result is used as mf result if the mf parameter has no ar property
    let mfrvars = if isWild rvar then if null arvars then [(rvar,mfIsNotAr)] else arvars else ((rvar,mfIsNotAr) : arvars)
    return (processMFpropForBindsPairs cnt mfpbps, processMFpropForPatterns mfrvars)
    where rt = getResultType fdes
          pdess = parsOfFuncDesc fdes
          hasMf pdes = elem "mf" $ propOfParamDesc pdes
          mfIsNotAr = any (\pdes -> (hasMf pdes) && not (isAddResultParam pdes)) pdess

fvGB :: GenBnd -> [CCS.VarName]
fvGB b = [] -- TODO using conversion to raw and CS.fvB

transUnOp :: LC.CUnaryOp -> CCS.OpName
transUnOp LC.CPreIncOp = "+"
transUnOp LC.CPreDecOp = "-"
transUnOp LC.CPostIncOp = "+"
transUnOp LC.CPostDecOp = "-"
transUnOp LC.CPlusOp = "+"
transUnOp LC.CMinOp  = "-"
transUnOp LC.CCompOp = "complement"
transUnOp LC.CNegOp  = "not"

transBinOp :: LC.CBinaryOp -> CCS.OpName
transBinOp LC.CMulOp = "*"
transBinOp LC.CDivOp = "/"
transBinOp LC.CRmdOp = "%"
transBinOp LC.CAddOp = "+"
transBinOp LC.CSubOp = "-"
transBinOp LC.CShlOp = "<<"
transBinOp LC.CShrOp = ">>"
transBinOp LC.CLeOp  = "<"
transBinOp LC.CGrOp  = ">"
transBinOp LC.CLeqOp = "<="
transBinOp LC.CGeqOp = ">="
transBinOp LC.CEqOp  = "=="
transBinOp LC.CNeqOp = "/="
transBinOp LC.CAndOp = ".&."
transBinOp LC.CXorOp = ".^."
transBinOp LC.COrOp  = ".|."
transBinOp LC.CLndOp = "&&"
transBinOp LC.CLorOp = "||"

transAssOp :: LC.CAssignOp -> CCS.OpName
transAssOp LC.CAssignOp = ""
transAssOp LC.CMulAssOp = "*"
transAssOp LC.CDivAssOp = "/"
transAssOp LC.CRmdAssOp = "%"
transAssOp LC.CAddAssOp = "+"
transAssOp LC.CSubAssOp = "-"
transAssOp LC.CShlAssOp = "<<"
transAssOp LC.CShrAssOp = ">>"
transAssOp LC.CAndAssOp = ".&."
transAssOp LC.CXorAssOp = ".^."
transAssOp LC.COrAssOp = ".|."

-- | Remove source from all but dummy expressions
cleanSrc :: GenExpr -> GenExpr
cleanSrc (GenExpr e o Nothing) = GenExpr (fmap cleanSrc e) o Nothing
cleanSrc (GenExpr e o (Just src)) =
    case e of
         CS.App (GenExpr (CS.Var "gencotDummy") _ _) _ _ -> GenExpr (fmap cleanSrc e) o (Just src)
         _ -> GenExpr (fmap cleanSrc e) o Nothing

-- | Construct a function's parameter type from the sequence of translated C parameter types.
-- The result is either the unit type, a single type, or a tuple type (for more than 1 parameter).
mkParType :: [GenType] -> GenType
mkParType [] = genType CS.TUnit
mkParType [gt] = gt
mkParType gts = genType $ CS.TTuple gts 

mkGenExpr :: [GenExpr] -> GenExpr
mkGenExpr [] = genExpr CS.Unitel
mkGenExpr [re] = re
mkGenExpr res = genExpr $ CS.Tuple res

{-
mkRawExpr :: [RawExpr] -> RawExpr
mkRawExpr [] = CS.RE CS.Unitel
mkRawExpr [re] = re
mkRawExpr res = CS.RE $ CS.Tuple res
-}

setBoxed :: GenType -> GenType
setBoxed (GenType (CS.TCon nam p _) o) = (GenType (CS.TCon nam p markBox) o)
setBoxed (GenType (CS.TRecord rp fields _) o) = (GenType (CS.TRecord rp fields markBox) o)
setBoxed (GenType (CS.TUnbox (GenType t _)) o) = (GenType t o)

setUnboxed :: GenType -> GenType
setUnboxed (GenType (CS.TCon nam p _) o) = (GenType (CS.TCon nam p markUnbox) o)
setUnboxed (GenType (CS.TRecord rp fields _) o) = (GenType (CS.TRecord rp fields markUnbox) o)
setUnboxed (GenType t o) = (GenType (CS.TUnbox (GenType t noOrigin)) o)

isUnboxed :: GenType -> Bool
isUnboxed (GenType (CS.TCon _ _ CCT.Unboxed) _) = True
isUnboxed (GenType (CS.TRecord _ _ CCT.Unboxed) _) = True
isUnboxed (GenType (CS.TUnbox _) _) = True
isUnboxed _ = False

markBox = CCT.Boxed False Nothing
markUnbox = CCT.Unboxed

isReadOnly :: GenType -> Bool
isReadOnly (GenType (CS.TBang t) _) = True
isReadOnly _ = False

isString :: GenType -> Bool
isString (GenType (CS.TBang t) _) = isString t
isString (GenType (CS.TCon "String" _ _) _) = True
isString _ = False

setOrigin :: LCN.NodeInfo -> GenType -> GenType
setOrigin n t = (GenType (typeOfGT t) $ mkOrigin n)

remComment :: GenType -> GenType
remComment (GenType t o) = GenType t $ toNoComOrigin o

errType :: String -> FTrav GenType
errType s = return $ genType $ CS.TCon ("err-" ++ s) [] markUnbox
