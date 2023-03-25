{-# LANGUAGE PackageImports #-}
module Gencot.Cogent.Translate where

import Control.Monad (liftM,filterM,when)
import Data.List as L (isPrefixOf,isInfixOf,intercalate,unlines,sortOn,sort,find)
import Data.Map as M (Map,singleton,unions,toList,union)
import Data.Maybe (catMaybes,fromJust,fromMaybe)

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
  transTagName, transObjName, transDeclName, mapIfUpper, mapNameToUpper, mapNameToLower, mapPtrDeriv, mapPtrVoid, mapMayNull, mapArrDeriv, mapFunDeriv,
  arrDerivHasSize, arrDerivCompNam, arrDerivToUbox, mapUboxStep, rmUboxStep, mapMayNullStep, rmMayNullStepThroughRo, addMayNullStep, 
  mapPtrStep, mapFunStep, mapIncFunStep, mapArrStep, mapModStep, mapRoStep, mapNamFunStep,
  getFileName, globStateType, isNoFunctionName, heapType, heapParamName, variadicParamName)
import Gencot.Items.Types (
  ItemAssocType, isNotNullItem, isReadOnlyItem, isNoStringItem, isHeapUseItem, isConstValItem, getItemProperties,
  getIndividualItemId, getObjectItemId, getParamSubItemId, getGlobalStateSubItemIds, getGlobalStateId,
  getGlobalStateProperty, getTagItemAssoc, getIndividualItemAssoc, getTypedefItemAssoc, adjustItemAssocType,
  getMemberSubItemAssoc, getRefSubItemAssoc, getResultSubItemAssoc, getElemSubItemAssoc, getParamSubItemAssoc, 
  getItemAssocType, getMemberItemAssocTypes, getSubItemAssocTypes, numberList, getAddResultProperties)
import Gencot.Items.Identifier (
  localItemId, memberSubItemId, elemSubItemId, refSubItemId, resultSubItemId,
  getParamName, getObjFunName, isToplevelObjectId, isParameterId)
import Gencot.Cogent.Ast
import Gencot.Cogent.Bindings (
  BindsPair, valVar, leadVar, lvalVar, resVar,
  mkBodyExpr, mkPlainExpr,
  mkEmptyBindsPair, mkDummyBindsPair, mkUnitBindsPair, mkDefaultBindsPair, mkIntLitBindsPair, mkCharLitBindsPair, mkStringLitBindsPair,
  mkValVarBindsPair, mkMemBindsPair, mkIdxBindsPair, mkOpBindsPair, mkConstAppBindsPair, mkAppBindsPair, mkAssBindsPair,
  mkIfBindsPair, mkTupleBindsPair, mkDerefBindsPair, mkFunDerefBindsPair, concatBindsPairs,
  processMFpropForBindsPairs,
  replaceBoundVarType,
  mkDummyBinding, mkNullBinding, mkExpBinding, mkRetBinding, mkBreakBinding, mkContBinding, 
  mkIfBinding, mkSwitchBinding, mkCaseBinding, mkSeqBinding, mkDecBinding, mkForBinding,
  mkTuplePattern, mkVarPattern, mkVarTuplePattern,
  mkAlt,
  processMFpropForPatterns)
import Gencot.Cogent.Expr (TypedVar(TV), typOfTV, namOfTV, mkUnitExpr, mkVarExpr, mkExpVarTupleExpr)
import Gencot.Cogent.Types (
  genType, mkConstrType, mkTypeName, mkU32Type, mkBoolType, mkTupleType, mkFunType, mkArrayType, mkRecordType,
  addTypeSyn, mkReadonly, mkUnboxed, isArrayType, isUnboxed, mkMayNull, getBoxType, getNnlType, getResultType)
import Gencot.Cogent.Postproc (postproc)
import qualified Gencot.C.Ast as LQ (Stm(Exp,Block), Exp)
import qualified Gencot.C.Translate as C (transStat, transExpr, transArrSizeExpr, transBlockItem)
import Gencot.Traversal (
  FTrav, markTagAsNested, isMarkedAsNested, hasProperty, getProperties, stopResolvTypeName,
  getFunDef, setFunDef, clrFunDef, enterItemScope, leaveItemScope, registerItemId, nextVarNum, resetVarNums,
  getValCounter, getCmpCounter, resetVarCounters, resetValCounter, getTConf)
import Gencot.Util.Types (
  carriedTypes, isExtern, isCompOrFunc, isCompPointer, isNamedFunPointer, isFunPointer, isPointer, isAggregate, isFunction, 
  isTypeDefRef, isComplete, isArray, isVoid, isTagRef, containsTypedefs, resolveTypedef, isComposite, 
  isLinearType, isLinearParType, isReadOnlyType, isReadOnlyParType, isDerivedType, isExternTypeDef, wrapFunAsPointer, getTagDef)
import Gencot.Util.Expr (checkForTrans, getFreeInCExpr, getFreeInCStat)
import Gencot.Util.Decl (localVarDecl)

{- genExpr e = GenExpr e noOrigin Nothing -}

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
           return $ wrapOrigin n ([GenToplv (CS.TypeDec tn [] $ mkRecordType ms) noOrigin] ++ nts)
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
           return $ [GenToplv (CS.TypeDec tn [] mkU32Type) $ mkOrigin n]
-- Translate an object or complete function declaration of the form
-- > typ name;
-- (where typ may be a derived type syntactically integrated in the name)
-- to a Cogent abstract function definition of the form
-- > name : funtyp
-- If the C object is not a function, the Cogent function is a parameterless
-- access function of type () -> typ
transGlobal de@(LCA.DeclEvent decl@(LCA.Declaration (LCA.Decl _ n))) | isComplete dtyp = do
    f <- transDeclName decl
    sfn <- getFileName
    let iat = getIndividualItemAssoc decl sfn
    t <- transType iat
-- from nesttags:
--    nt <- transTagIfNested dtyp n
    let typ = if isFunction dtyp then t else mkConstFunType t
    if isFunction dtyp -- suppress generation of access function
       then return $ wrapOrigin n ({-nt ++ -}[GenToplv (CS.AbsDec f (CS.PT [] [] typ)) noOrigin])
       else return $ []
    where dtyp = LCA.declType decl
-- Translate a C function definition of the form
-- > rt name(parlist) { stmt }
-- to a Cogent function definition of the form
-- > name :: (partypes) -> rt
-- > name (parnames) = expr
-- where @expr@ is the translation of @stmt@ and
-- @partypes@, @rt@, and @expr@ are modified according to a parameter modification description.
transGlobal (LCA.DeclEvent idecl@(LCA.FunctionDef (LCA.FunDef decl stat n))) = do
    f <- transDeclName idecl
    sfn <- getFileName
    let iat@(fid,_) = getIndividualItemAssoc idecl sfn
    fdes <- getFuncDesc iat
-- from nesttags:
--    nt <- transTagIfNested typ n -- wirkt erst wenn transTagIfNested auch derived types verarbeitet
--    ps <- transParamNames iat isVar pars
    LCA.enterFunctionScope
    LCA.defineParams LCN.undefNode decl
    enterItemScope
    registerParamIds pars 1 fid
    setFunDef idecl
    alts <- transBody fdes stat
--    e <- extendExpr iat e pars
    clrFunDef
    resetVarNums
    leaveItemScope
    LCA.leaveFunctionScope
    return $ wrapOrigin n ({-nt ++ -}[GenToplv (CS.FunDef f (CS.PT [] [] (typeOfFuncDesc fdes)) alts) noOrigin])
    where typ@(LCA.FunctionType (LCA.FunType _ pars _) _) = LCA.declType idecl
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
    f <- transDeclName odef
    sfn <- getFileName
    let iat = getIndividualItemAssoc odef sfn
    gs <- getGlobalStateProperty $ fst iat
    tsyn <- if null gs 
               then return $ []
               else do
                   pt <- transType $ adjustItemAssocType iat
                   return $ [GenToplv (CS.TypeDec (globStateType gs) [] $ rmMayNullIf True pt) noOrigin]
    t <- transType iat
-- from nesttags:
--    nt <- transTagIfNested dtyp n
    let afun = [] -- [GenToplv (CS.AbsDec f (CS.PT [] [] $ mkConstFunType t)) noOrigin]
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
    return $ [GenToplv (CS.ConstDef en mkU32Type e) $ mkOrigin n]
-- Translate a typedef of the form
-- > typedef type-specifier declarator;
-- where @declarator@ denotes a (derived type for an) identifier @idnam@.
-- If the @type-specifier@ denotes a struct or union type the typedef is first adjusted to the derived pointer type.
-- Array types need no adjusting, they are always adjusted by @transType@.
-- The translation result has the form
-- > type idnam = type
-- where @type@ is constructed by translating @type-specifier@ and applying all derivations from the adjusted @declarator@.
-- A MayNull application to @type@ is removed.
transGlobal (LCA.TypeDefEvent (LCA.TypeDef idnam typ _ n)) = do
    t <- if isArray typ
            then transArrayType modifiat -- prevent making readonly
            else transType modifiat
    nt <- transTagIfNested iat n
    let dt = getNnlType t
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
    where getSyn (GenType _ _ (Just nam)) = nam
          getSyn (GenType (CS.TBang t) _ _) = getSyn t
          getSyn (GenType (CS.TUnbox t) _ _) = getSyn t
          getSyn t = getName t
          getName (GenType (CS.TCon nam _ _) _ _) = nam
          getName (GenType (CS.TBang t) _ _) = getName t
          getName (GenType (CS.TUnbox t) _ _) = getName t
          genMap :: ItemAssocType -> FTrav (Map String ItemAssocType)
          genMap iat = do
              gt <- transType iat
              return $ M.union (singleton (getSyn gt) iat) (singleton (getName gt) iat)

-- | Generate type definitions for a Cogent type name @nam@ used by a derived array or function pointer type.
-- Additional argument is the original C type as an ItemAssocType.
genDerivedTypeDefs :: String -> ItemAssocType -> FTrav [GenToplv]
-- For a derived array type the name has the form @CArr<size>@, @CArrX<size>X@ or @CArrXX@.
-- The last case is ignored.
-- For the other cases a generic type defintion is generated of the form
-- > type CArr... el = { arr...: el#[<size>] }
genDerivedTypeDefs nam (_,(LCA.ArrayType _ as _ _)) | arrDerivHasSize nam = do
    e <- transExpr $ getSizeExpr as
    return [GenToplv (CS.TypeDec nam ["el"] $ mkArrayType nam e $ genType $ CS.TVar "el" False False) noOrigin]
    where getSizeExpr (LCA.ArraySize _ e) = e -- arrDerivHasSize implies that only this case may occur for the array size as.
-- For a derived function pointer type the name has the form @CFunPtr_enc@ or @CFunInc_enc@ where
-- @enc@ is an encoded C type. First we determine the name with all typedef names resolved.
-- If it differs from @nam@ then @nam@ contains typedef names. In that case generate a type synonym definition
-- > type nam = resnam
-- where resnam is the name in the type. Otherwise generate an abstract type definition of the form
-- > type nam
-- In the case of a complete function type additionally introduce a synonym for the corresponding
-- function type of the form
-- > type CFun_enc = <Cogent mapping of C function type>
genDerivedTypeDefs nam iat@(iid,pt@(LCA.PtrType _ _ _)) = do
    typ <- transType iat
    let isResolved = getName typ == nam
    let tdef = if isResolved
                then CS.AbsTypeDec nam [] []
                else CS.TypeDec nam [] $ rmSyn typ
    sub <- getRefSubItemAssoc iat
    typ <- transType sub
    let fdef = GenToplv (CS.TypeDec fnam [] typ ) noOrigin
    return $ (GenToplv tdef noOrigin): if (mapFunDeriv True) `isPrefixOf` nam then [fdef] else []
    where fnam = "CFun" ++ (drop (length (mapFunDeriv True)) nam)
          getName (GenType (CS.TCon nam _ _) _ _) = nam
          getName (GenType (CS.TBang t) _ _) = getName t
          getName (GenType (CS.TUnbox t) _ _) = getName t
          rmSyn (GenType (CS.TBang t) o _) = GenType (CS.TBang (rmSyn t)) o Nothing
          rmSyn (GenType (CS.TUnbox t) o _) = GenType (CS.TUnbox (rmSyn t)) o Nothing
          rmSyn (GenType t o _) = GenType t o Nothing
genDerivedTypeDefs _ _ = return []

{-
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
-}

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
transMember :: ItemAssocType -> LCA.MemberDecl -> FTrav (CCS.FieldName, GenType)
transMember iat mdecl@(LCA.MemberDecl (LCA.VarDecl (LCA.VarName idnam _) _ _) _ n) = do
    t <- if isArray mtyp
            then transArrayType miat -- prevent making readonly
            else transType miat
    let ut = if isArray mtyp then getBoxType t else t
    mnam <- mapIfUpper idnam
    return (mnam, setOrigin n ut)
    where miat@(_,mtyp) = getMemberSubItemAssoc iat mdecl
{- LCA.AnonBitField cannot occur since it is always replaced by aggBitfields -}

{-
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
-}

-- | Translate a C type specification to a Cogent type.
-- The C type is specified as an ItemAssocType, so that its item properties can be respected.
transType :: ItemAssocType -> FTrav GenType

-- Type void:
-- Translate to: ()
transType (_, (LCA.DirectType LCA.TyVoid _ _)) =
    return unitType
-- Direct type:
-- Translate to: Name of primitive type (boxed) or composite type (unboxed).
-- Remark: Semantically, primitive types are unboxed. 
-- However, if marked as unboxed the Cogent prettyprinter adds a (redundant) unbox operator.
transType (_, (LCA.DirectType tnam _ _)) = do
    tn <- transTNam tnam
    let bt = mkTypeName tn
    let t = case tnam of
                (LCA.TyComp _) -> mkUnboxed bt
                _ -> bt
    return t
-- Typedef name:
-- If external typedef where resolve does not stop, ignore the typedef name.
-- Translate the referenced type, using the typedef names collective item id, if not ignored.
-- Additionally apply Not-Null and Read-Only properties of specific item id.
-- If not ignored translate typedef name to mapped name and insert into translated type.
transType iat@(iid, (LCA.TypeDefType (LCA.TypeDefRef idnam typ _) _ _)) = do
    dt <- LCA.getDefTable
    srtn <- stopResolvTypeName idnam
    let ignoreTypeName = (isExternTypeDef dt idnam) && not srtn
    -- translate type, use typedef name as item id if not ignored
    let rslviat = (if not ignoreTypeName then getTypedefItemAssoc idnam typ else (iid,typ))
    t <- transType rslviat
    -- handle typedef name
    ts <- if ignoreTypeName
             then return t
             else do
                 tn <- mapNameToUpper idnam
                 return $ addTypeSyn tn t
    -- handle Not-Null and Read-Only property of specific iid
    safe <- isNotNullItem iat
    ro <- isReadOnlyItem iat
    return $ makeReadOnlyIf ro $ rmMayNullIf safe ts
-- Pointer to void:
-- Translate to: CVoidPtr
-- If no Not-Null property: MayNull CVoidPtr
-- If Read-Only property: banged
transType iat@(_, (LCA.PtrType t _ _)) | isVoid t = do
    safe <- isNotNullItem iat
    ro <- isReadOnlyItem iat
    return $ makeReadOnlyIf ro $ addMayNullIfNot safe $ mkTypeName mapPtrVoid
-- Derived pointer type for function type t:
-- Encode t, apply CFunPtr or CFunInc, add synonym if different, and make unboxed.
transType iat@(_, (LCA.PtrType t _ _)) | isFunction t = do
    sub <- getRefSubItemAssoc iat
    (et1,et2) <- encodeType sub
    let tn = mkTypeName ((mapFunDeriv $ isComplete t) ++ "_" ++ et2)
    let stn = if et1 == et2 then tn else addTypeSyn et1 tn
    return $ mkUnboxed stn
-- Derived pointer type for array type t:
-- Translate t and use as result. Always boxed.
-- If no Not-Null property: apply MayNull
-- If Read-OnlyProperty: banged
transType iat@(_, (LCA.PtrType t _ _)) | isArray t = do
    safe <- isNotNullItem iat
    ro <- isReadOnlyItem iat
    sub <- getRefSubItemAssoc iat
    typ <- transType sub
    return $ makeReadOnlyIf ro $ addMayNullIfNot safe typ
-- Derived pointer type for (unsigned) char type:
-- If Read-Only property and not No-String property: translate to primitive type String
-- Otherwise translate to normal pointer (to U8).
transType iat@(_, pt@(LCA.PtrType (LCA.DirectType (LCA.TyIntegral it) _ _) _ _)) | it == TyChar || it == TyUChar = do
    ro <- isReadOnlyItem iat
    ns <- isNoStringItem iat
    if ro && (not ns)
       then return $ mkTypeName "String"
       else do
           safe <- isNotNullItem iat
           sub <- getRefSubItemAssoc iat
           typ <- transType sub
           return $ makeReadOnlyIf ro $ addMayNullIfNot safe $ mkConstrType mapPtrDeriv [typ]
-- Derived pointer type for other type t:
-- Translate t. If unboxed and no function pointer make boxed, otherwise apply CPtr. Always boxed.
-- If no Not-Null property: apply MayNull
-- If Read-OnlyProperty: banged
transType iat@(_, pt@(LCA.PtrType t _ _)) = do
    safe <- isNotNullItem iat
    ro <- isReadOnlyItem iat
    sub <- getRefSubItemAssoc iat
    typ <- transType sub
    let rtyp = if (isUnboxed typ) && not (isFunPointer t) 
                then getBoxType typ
                else mkConstrType mapPtrDeriv [typ]
    return $ makeReadOnlyIf ro $ addMayNullIfNot safe rtyp
-- Complete derived function type: ret (p1,..,pn)
-- Translate ret, determine parameter description including virtual parameters.
-- Translate to: Cogent function type from parameter tuple to extended result tuple.
transType iat@(_, (LCA.FunctionType (LCA.FunType ret pars variadic) _)) = do
    sub <- getResultSubItemAssoc iat
    r <- transType sub
    pdess <- getAllParamDesc iat
    return $ genFunType pdess r
-- Incomplete derived function type: ret ()
-- Signal an error.
transType iat@(iid, (LCA.FunctionType (LCA.FunTypeIncomplete ret) _)) =
    error ("Cannot translate incomplete function type for " ++ iid)
-- Derived array type for element type t:
-- Translate with transArrayType, always boxed.
-- If Read-OnlyProperty: apply bang.
transType iat@(_, (LCA.ArrayType t as _ _)) = do
    res <- transArrayType iat
    ro <- isReadOnlyItem iat
    return $ makeReadOnlyIf ro res

-- | Reduced translation for array types.
-- The interpretation of Read-Only properties is omitted.
-- This is used when the array type shall be used in its unboxed form.
-- Translate t, if again array type make unboxed.
-- If array size is unknown translate to abstract type CArrXX el.
-- Otherwise translate array size expression.
-- Then create wrapper record around builtin array type with size expression
-- and add generic Gencot array type as synonym.
-- Always boxed.
transArrayType :: ItemAssocType -> FTrav GenType
transArrayType iat@(_, (LCA.ArrayType t as _ _)) = do
    sub <- getElemSubItemAssoc iat
    typ <- if isArray t then transArrayType sub else transType sub
    let eltyp = if isArray t then mkUnboxed typ else typ
    siz <- case as of
                 LCA.UnknownArraySize _ -> return mkUnitExpr
                 LCA.ArraySize _ e -> transExpr e
    return $ mkArrayType (mapArrDeriv as) siz eltyp

-- | Encode a C type specification as a Cogent type name.
-- The C type is specified as an ItemAssocType, so that its item properties can be respected.
-- The result is a pair of the encoding with typedef names and without typedef names.
encodeType :: ItemAssocType -> FTrav (String,String)
-- Type void:
-- Encode as: Void
encodeType (_, (LCA.DirectType LCA.TyVoid _ _)) =
    return ("Void","Void")
-- Direct type:
-- Encode as: Name of primitive type or composite type.
-- For composite type prepend unbox step.
encodeType (_, (LCA.DirectType tnam _ _)) = do
    tn <- transTNam tnam
    let res = ustep ++ tn
    return (res,res)
    where ustep = case tnam of
                (LCA.TyComp _) -> mapUboxStep
                _ -> ""
-- Typedef name:
-- For the second result encode the referenced type.
-- For the first result encode as mapped name. For struct, union, or array prepend unbox step.
-- If the typedef name has the Not-Null property, omit or remove MayNull step
-- otherwise move a MayNull step from the resolved type to the mapped name.
-- If the typedef name has the Read-Only property add readonly step (simplifying also for String types).
encodeType iat@(iid, (LCA.TypeDefType (LCA.TypeDefRef idnam typ _) _ _)) = do
    dt <- LCA.getDefTable
    srtn <- stopResolvTypeName idnam
    let ignoreTypeName = (isExternTypeDef dt idnam) && not srtn
    safe <- isNotNullItem iat
    ro <- isReadOnlyItem iat
    let rslviat = (if not ignoreTypeName then getTypedefItemAssoc idnam typ else (iid,typ))
    (_,rslvtyp) <- encodeType rslviat
    tn <- mapNameToUpper idnam
    let nntyp = (addMayNullStepIfNot (safe || (not $ hasMayNullStep rslvtyp)) (ustep ++ tn),
                 rmMayNullStepIf safe rslvtyp)
    return (if ro then fmap (addReadOnlyStepIf ro) nntyp else nntyp)
    where ustep = if isAggregate typ then mapUboxStep else ""
-- Derived pointer type for function type t:
-- Encode t, prepend pointer derivation step.
encodeType iat@(_, (LCA.PtrType t _ _)) | isFunction t = do
    sub <- getRefSubItemAssoc iat
    (tn1,tn2) <- encodeType sub
    return (mapPtrStep ++ tn1, mapPtrStep ++ tn2)
-- Derived pointer type for (unsigned) char type:
-- If Read-Only property and not No-String property: encode as "String"
-- Otherwise encode as normal pointer (to U8).
encodeType iat@(_, pt@(LCA.PtrType (LCA.DirectType (LCA.TyIntegral it) _ _) _ _)) | it == TyChar || it == TyUChar = do
    ro <- isReadOnlyItem iat
    ns <- isNoStringItem iat
    if ro && (not ns)
       then return ("String","String")
       else do
           safe <- isNotNullItem iat
           sub <- getRefSubItemAssoc iat
           (tn1,tn2) <- encodeType sub
           return $ fmap (addReadOnlyStepIf ro . addMayNullStepIfNot safe) (mapPtrStep ++ tn1, mapPtrStep ++ tn2)
-- Derived pointer type for other type t:
-- Encode t, for aggregate type remove unbox step, otherwise prepend pointer derivation step.
-- If no Not-Null property, add MayNull step.
-- If Read-Only property  add readonly step.
encodeType iat@(_, pt@(LCA.PtrType t _ _)) = do
    safe <- isNotNullItem iat
    ro <- isReadOnlyItem iat
    sub <- getRefSubItemAssoc iat
    tnp <- encodeType sub
    let htn = if isAggregate t then fmap rmUboxStep tnp else fmap (mapPtrStep ++) tnp
    return $ fmap (addReadOnlyStepIf ro . addMayNullStepIfNot safe) htn
-- Complete derived function type: ret (p1,..,pn)
-- Encode ret, prepend function derivation step using encoded pi.
encodeType iat@(_, (LCA.FunctionType (LCA.FunType ret pars variadic) _)) = do
    sub <- getResultSubItemAssoc iat
    (tn1,tn2) <- encodeType sub
    epps <- mapM (encodeParamType iat) $ numberList pars
    let (ep1s,ep2s) = unzip epps
    let (vp1s,vp2s) = if variadic then (ep1s ++ [mapRoStep ++ variadicTypeName], ep2s ++ [mapRoStep ++ variadicTypeName]) else (ep1s,ep2s)
    arProps <- getAddResultProperties iat
    let varProps = if variadic then arProps ++ [False] else arProps
    let ps1s = map (\(arProp,s) -> if arProp then mapModStep ++ s else s) $ zip varProps vp1s
    let ps2s = map (\(arProp,s) -> if arProp then mapModStep ++ s else s) $ zip varProps vp2s
    return $ ((mapFunStep ps1s) ++ tn1, (mapFunStep ps2s) ++ tn2)
-- Incomplete derived function type: ret ()
-- Encode ret, prepend incomplete function derivation step.
encodeType iat@(_, (LCA.FunctionType (LCA.FunTypeIncomplete ret) _)) = do
    sub <- getResultSubItemAssoc iat
    tnp <- encodeType sub
    return $ fmap (mapIncFunStep ++) tnp
-- Derived array type for element type t:
-- Encode t, prepend array derivation step and unbox step.
-- If Read-Only property add readonly step.
encodeType iat@(_, (LCA.ArrayType t as _ _)) = do
    ro <- isReadOnlyItem iat
    sub <- getElemSubItemAssoc iat
    tnp <- encodeType sub
    return $ fmap (addReadOnlyStepIf ro . ((mapUboxStep ++ (mapArrStep as)) ++)) tnp

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
rmMayNullIf True t = getNnlType t
rmMayNullIf False t = t

addMayNullIfNot :: Bool -> GenType -> GenType
addMayNullIfNot False t = mkMayNull t
addMayNullIfNot True t = t

rmMayNullStepIf :: Bool -> String -> String
rmMayNullStepIf True t = rmMayNullStepThroughRo t
rmMayNullStepIf False t = t
    
addMayNullStepIfNot :: Bool -> String -> String
addMayNullStepIfNot False t = addMayNullStep t
addMayNullStepIfNot True t = t

hasMayNullStep :: String -> Bool
hasMayNullStep t = (mapMayNullStep `isPrefixOf` t) || ((mapRoStep ++ mapMayNullStep) `isPrefixOf` t)

makeReadOnlyIf :: Bool -> GenType -> GenType
makeReadOnlyIf True t = mkReadonly t
makeReadOnlyIf False t = t

addReadOnlyStepIf :: Bool -> String -> String
addReadOnlyStepIf True t@('R' : '_' : _) = t
addReadOnlyStepIf True t = mapRoStep ++ t
addReadOnlyStepIf False t = t

{-
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
applyProperties iat (GenType (CS.TFun pt rt) o _) = do
    arProps <- getAddResultProperties iat
    let artypes = map snd $ filter fst $ zip arProps ptl
    gspars <- makeGlobalStateParams iat
    gstypes <- mapM makeGlobalStateType $ map (snd . fst) gspars
    gsartypes <- mapM makeGlobalStateType $ map (snd . fst) $ filter snd gspars
    huProp <- isHeapUseItem iat
    let hutype = if huProp then [makeHeapType] else []
    let allpartypes = ptl ++ gstypes ++ hutype
    let arpartypes = artypes ++ gsartypes ++ hutype
    return $ GenType (CS.TFun (mkParType allpartypes) (mkParType $ addPars rt $ map remComment $ arpartypes)) o Nothing
    where addPars (GenType CS.TUnit _ _) ps = ps
          addPars r ps = r : ps
          ptl = ptlist pt
          ptlist (GenType CS.TUnit _ _) = []
          ptlist (GenType (CS.TTuple ts) _ _) = ts
          ptlist gt = [gt]

shallAddResultGS :: GenType -> Bool
shallAddResultGS t = not $ isReadOnly t

-- | Determine the Cogent type from the item associated type of a global state parameter
-- The type is ignored, the Cogent type is determined from the Global-State property only.
makeGlobalStateType :: ItemAssocType -> FTrav GenType
makeGlobalStateType iat@(iid,_) = do
    ro <- isReadOnlyItem iat
    gs <- getGlobalStateProperty iid
    return $ makeReadOnlyIf ro $ mkTypeName (globStateType gs)
-}

makeHeapType :: GenType
makeHeapType = mkTypeName heapType

-- | Convert an arbitrary Cogent type T to the function type () -> T
mkConstFunType :: GenType -> GenType
mkConstFunType t = mkFunType unitType t

variadicType = makeReadOnlyIf True $ mkTypeName variadicTypeName
variadicTypeName = "VariadicCogentParameters"

-- | Encode a type as parameter type.
-- The parameter declaration is specified together with the parameter position.
-- For an array type: adjust by removing unbox step.
-- For a function type: adjust by adding pointer step.
encodeParamType :: ItemAssocType -> (Int,LCA.ParamDecl) -> FTrav (String, String)
encodeParamType iat ipd@(_,pd) = do
    typp <- encodeType $ getParamSubItemAssoc iat ipd
    if isArray $ LCA.declType pd
       then return $ fmap rmUboxStep typp
       else return typp

{-
arraySizeType :: LCA.ArraySize -> GenType
arraySizeType (LCA.ArraySize _ (LCS.CConst (LCS.CIntConst ci _))) =
    mkTypeName tnam
    where tnam = if i < 257 then "U8" else if i < 65537 then "U16" else "U32"
          i = LC.getCInteger ci
arraySizeType _ = mkU32Type
-}

{- Translating function bodies -}
{- --------------------------- -}

-- | Retrieve the C type of a C expression.
-- The StmtCtxs are only used for CStatExpr which are not processed by Gencot, therefore we omit them.
-- If the ExprSide is LValue, tExpr checks whether the expression is admissible as lvalue,
-- Therefore we always use RValue so that all expressions are accepted.
exprType :: LC.CExpr -> FTrav LCA.Type
exprType e = LCA.tExpr [] RValue e

transBody :: FuncDesc -> LC.CStat -> FTrav [GenAlt]
transBody fdes s = do
    resetVarCounters
    tconf <- getTConf
    b <- bindStat s
    let e = cleanSrc $ postproc tconf $ mkBodyExpr b $ genFunResultExpr fdes
    return [mkAlt (genFunParamPattern fdes) e]
{-
transBody :: ItemAssocType -> LC.CStat -> [LCA.ParamDecl] -> FTrav GenExpr
transBody fiat s pars = do
    resetVarCounters
    tconf <- getTConf
    b <- bindStat s
    riat <- getResultSubItemAssoc fiat
    let r = if isVoid $ snd riat then mkUnitExpr else mkVarExpr (TV resVar unitType) -- resVar
    e <- error "" {-extendExpr fiat r pars-}
    return $ cleanSrc $ postproc tconf $ mkBodyExpr b e
-}

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

-- | Processing a declaration together with the following block content.
bindDecl :: LC.CDecl -> [LC.CBlockItem] -> FTrav GenBnd
bindDecl dc@(LC.CDecl specs dcs _) bis = do
    -- Here it would be easiest to use LCA.analyseDecl and then process the declarators.
    -- However, that would insert the defined identifiers of all declarators into the symbol table.
    -- When processing a declarator afterwards it could happen that an identifier used in an initializer
    -- is looked up in the wrong scope.
    -- Therefore the function bindDeclrs re-implements the content of LCA.analyseDecl for every declarator.
    pspecs <- processDeclSpecs specs
    bnd <- bindDeclrs pspecs dcs bis
    insertBlockItemsSrc ((LC.CBlockDecl dc) : bis) bnd
bindDecl sa@(LC.CStaticAssert _ _ _) bis = 
    insertBlockItemsSrc ((LC.CBlockDecl sa) : bis) $ mkDummyBinding "Static assertions not supported"

-- | Process declaration specifiers.
-- Content copied from LCA.analyseDecl.
processDeclSpecs :: [LC.CDeclSpec] -> FTrav ProcDeclSpecs
processDeclSpecs specs = do
    let (sspecs, attrs, tquals, tspecs, fspecs, _) = LCS.partitionDeclSpecs specs
    ctspecs <- LCA.canonicalTypeSpec tspecs
    return (sspecs, attrs, tquals, ctspecs, fspecs)

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
    return $ mkDecBinding v bp bs

-- | Process a single declarator.
-- The content copies the relevant steps from LCA.analyseDecl.
bindDeclr :: ProcDeclSpecs -> DeclElem -> FTrav (TypedVar,BindsPair)
bindDeclr (ss,a,tq,tsa,fs) (Just declr@(LC.CDeclr (Just nam) _ _ _ _),mi,me) = do
    v <- mapIfUpper nam
    vardeclInfo@(VarDeclInfo _ _ _ _ typ _) <-
        LCA.analyseVarDecl False ss a tq tsa fs declr [] Nothing

    num <- nextVarNum s  -- not yet used
    -- bindDeclr is only used for local declarations, therefore the function context is defined
    (Just fdef) <- getFunDef
    sfn <- getFileName
    let fid = getIndividualItemId fdef sfn -- not yet used
        vid = (localItemId s) -- here num and fid must be used when local item ids are changed.

    t <- transType (vid,typ)

    -- LCA.tInit only checks the initializer, it is not needed here.

    bp <- bindInit mi t

    -- this inserts the new variable into the symbol table, hence it must be done after processing mi by bindInit
    -- it does the same as function localVarDecl in module LCA, but that is not exported, hence it has been copied in Gencot.Util.Decl.
    localVarDecl vardeclInfo mi
    
    registerItemId s vid
    return ((TV v t),bp)
    where s = LCI.identToString nam
bindDeclr _ _ = return ((TV "" unitType),mkEmptyBindsPair)

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
    t <- transType ("",ct)
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
    t <- transType (iid,ct)
    bp <-
       if (isToplevelObjectId iid) && (not $ isFunction ct) -- global variable
          then do
              gs <- getGlobalStateProperty iid
              if null gs
                 then do
                     cv <- isConstValItem (iid,ct)
                     if cv -- Const-Val property: invoke access function named v
                        then return $ mkConstAppBindsPair cnt v t
                        else -- assume preprocessor constant: access Cogent constant named v
                             return $ mkValVarBindsPair cnt $ TV v t
                 else do
                     fdes <- getContextFuncDesc
                     let pdes = searchGlobalStateParamDesc fdes gs
                     if null $ nameOfParamDesc pdes
                        then return $ mkDummyBindsPair cnt ("Cannot access global variable: " ++ (LCI.identToString nam))
                        else if isArrayType $ typeOfParamDesc pdes
                        then return $ mkValVarBindsPair cnt $ TV (nameOfParamDesc pdes) (typeOfParamDesc pdes)
                        else do
                            cntp <- getCmpCounter
                            return $ mkDerefBindsPair cntp $ mkValVarBindsPair cnt $ TV (nameOfParamDesc pdes) (typeOfParamDesc pdes)
          else return $ mkValVarBindsPair cnt $ TV v t
    insertExprSrc e bp
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
    let t1 = typOfTV (leadVar bp1)
    cnt <- getValCounter
    let c0 = mkIntLitBindsPair cnt t1 0
    cnt <- getValCounter
    let c1 = mkIntLitBindsPair cnt t1 1
    ct <- exprType e
    t <- transType ("",ct)
    insertExprSrc e $ mkIfBindsPair t (mkOpBindsPair mkBoolType "==" [bp1,c0]) c1 c0
bindExpr e@(LC.CUnary LC.CIndOp e1 _) = do
    bp1 <- bindExpr e1
    ct1 <- exprType e1
    bp <-
      if isFunPointer ct1
         then do
             iid <- getExprItemId e1
             ft <- transType (iid,ct1)
             return $ mkFunDerefBindsPair ft bp1
         else do
             cnt <- getCmpCounter
             return $ mkDerefBindsPair cnt bp1
    insertExprSrc e bp
bindExpr e@(LC.CUnary op e1 _) | elem op [LC.CPlusOp,LC.CMinOp,LC.CCompOp] = do
    bp1 <- bindExpr e1
    ct1 <- exprType e1
    t1 <- transType ("",ct1)
    insertExprSrc e $ mkOpBindsPair t1 (transUnOp op) [bp1]
bindExpr e@(LC.CUnary op e1 _) | elem op [LC.CPreIncOp,LC.CPreDecOp,LC.CPostIncOp,LC.CPostDecOp] = do
    bp1 <- bindExpr e1
    ct1 <- exprType e1
    t1 <- transType ("",ct1)
    cnt <- getValCounter
    let bp2 = mkIntLitBindsPair cnt t1 1
    ct <- exprType e
    t <- transType ("",ct)
    insertExprSrc e $ mkAssBindsPair post t (transUnOp op) bp1 bp2
    where post = elem op [LC.CPostIncOp,LC.CPostDecOp]
bindExpr e@(LC.CBinary LC.CLndOp e1 e2 _) = do
    -- e1 && e2 -> if e1 then e2 else 0
    bp1 <- bindExpr e1
    bp2 <- bindExpr e2
    ct2 <- exprType e2
    t2 <- transType ("",ct2)
    cnt <- getValCounter
    let c0 = mkIntLitBindsPair cnt t2 0
    insertExprSrc e $ mkIfBindsPair t2 bp1 bp2 c0
bindExpr e@(LC.CBinary LC.CLorOp e1 e2 _) = do
    -- e1 || e2 -> if e1 then 1 else e2
    bp1 <- bindExpr e1
    bp2 <- bindExpr e2
    ct2 <- exprType e2
    t2 <- transType ("",ct2)
    cnt <- getValCounter
    let c1 = mkIntLitBindsPair cnt t2 1
    insertExprSrc e $ mkIfBindsPair t2 bp1 c1 bp2
bindExpr e@(LC.CBinary op e1 e2 _) = do
    bp1 <- bindExpr e1
    bp2 <- bindExpr e2
    ct <- exprType e
    t <- transType ("",ct)
    insertExprSrc e $ mkOpBindsPair t (transBinOp op) [bp1,bp2]
bindExpr e@(LC.CCall f es _) = do
    bps <- mapM bindExpr es
    fbp <- bindExpr f
    cft <- exprType f
    iid <- getExprItemId f
    fbp' <- if isFunPointer cft
               then do
                   ft <- transType (iid,cft)
                   return $ mkFunDerefBindsPair ft fbp
               else return fbp
    fd <- getFuncDesc (iid,cft)
    (pbps,rpat) <- processParamVals (leadVar fbp') fd bps
    insertExprSrc e $ mkAppBindsPair fbp' rpat pbps
bindExpr e@(LC.CAssign op e1 e2 _) = do
    bp1 <- bindExpr e1
    bp2 <- bindExpr e2
    insertExprSrc e $ mkAssBindsPair False unitType (transAssOp op) bp1 bp2
bindExpr e@(LC.CCond e1 (Just e2) e3 _) = do
    bp1 <- bindExpr e1
    bp2 <- bindExpr e2
    bp3 <- bindExpr e3
    ct <- exprType e
    t <- transType ("",ct)
    insertExprSrc e $ mkIfBindsPair t bp1 bp2 bp3
bindExpr e@(LC.CComma es _) = do
    bps <- mapM bindExpr es
    insertExprSrc e $ concatBindsPairs bps
bindExpr e = do
    cnt <- getValCounter
    insertExprSrc e $ mkDummyBindsPair cnt "Translation of expression not yet implemented"

-- | Add a statement source to a binding
insertStatSrc :: LC.CStat -> GenBnd -> FTrav GenBnd
insertStatSrc src (CS.Binding ip t (GenExpr e o et _) v) = do
    src' <- C.transStat src
    return $ (CS.Binding ip t (GenExpr e o et (Just src')) v)

-- | Add an expression source to the final binding in the main list
-- The expression is inserted as an expression statement.
insertExprSrc :: LC.CExpr -> BindsPair -> FTrav BindsPair
insertExprSrc src (main,putback) = do
    src' <- C.transExpr src
    let srcstat = (LQ.Exp (Just src') noOrigin)
    return $ ((CS.Binding ip t (GenExpr e o et (Just srcstat)) v) : tail main,putback)
    where (CS.Binding ip t (GenExpr e o et _) v) = head main

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

-- | Description of a function: type, properties, parameter descriptions.
-- The parameter descriptions describe the C and virtual parameters in their original order.
data FuncDesc = FuncDesc {
    typeOfFuncDesc :: GenType,
    propOfFuncDesc :: [String],
    parsOfFuncDesc :: [ParamDesc]}

-- | Construct a function description from the functions item associated type
getFuncDesc :: ItemAssocType -> FTrav FuncDesc
getFuncDesc iat = do
    sub <- getResultSubItemAssoc iat
    rtyp <- transType sub
    props <- getItemProperties iat
    parms <- getAllParamDesc iat
    return $ FuncDesc (genFunType parms rtyp) props parms

-- | Construct the descriptions for all parameters of a function
-- The parameter types are not taken from the translated function type, because
-- there they may have been rearranged by processing a ModificationFunction property.
-- If parameter names are not available they are left empty, they are automatically not used in such situations.
getAllParamDesc :: ItemAssocType -> FTrav [ParamDesc]
getAllParamDesc iat@(iid,(LCA.FunctionType (LCA.FunType _ pds isVar) _)) = do
    pns <- mapM mapIfUpper $ map (\d -> case LCA.declName d of VarName idnam _ -> idnam; NoName -> LCI.builtinIdent "") pds
    pts <- mapM transType piats
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
-- The first string is the item id of the parameter.
-- The boolean is true if it has no ReadOnly property.
-- The second string is the GlobalState property.
makeGlobalStateParamDesc :: ((String, Bool), String) -> FTrav ParamDesc
makeGlobalStateParamDesc ((iid,noro), gs) = do
    name <- mapIfUpper $ LCI.Ident (getParamName iid) 0 LCN.undefNode
    gsvar <- getGlobalStateId gs -- global var item id or ""
    if null gsvar
       then do -- global variable not available, use type synonym as opaque type
         let typ = makeReadOnlyIf (not noro) $ mkTypeName (globStateType gs)
         props <- getProperties iid
         return $ ParamDesc name typ props
       else do -- global variable found, convert its type to pointer and add type synonym
         -- if the variable has an array type this is correct because transType ignores the pointer
         mdec <- LCA.lookupObject $ LCI.Ident (getObjFunName gsvar) 0 LCN.undefNode
         case mdec of
              Nothing -> return $ ParamDesc "" unitType []
              Just decl -> do
                  let piat = (iid,LCA.PtrType (LCA.declType decl) LCA.noTypeQuals LCA.noAttributes)
                  typ <- transType piat
                  props <- getItemProperties piat
                  return $ ParamDesc name (addTypeSyn (globStateType gs) typ) props

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
getTypedVarFromParamDesc pdes = TV (nameOfParamDesc pdes) $ typeOfParamDesc pdes

-- | Retrieve the description of the surrounding function when processing a function body.
-- Outside a function body a description with unit type and no parameters is returned.
getContextFuncDesc :: FTrav FuncDesc
getContextFuncDesc = do
    mfdef <- getFunDef
    case mfdef of
         Nothing -> return $ FuncDesc unitType [] []
         Just fdef -> do
             sfn <- getFileName
             let iat@(fid,_) = getIndividualItemAssoc fdef sfn
             getFuncDesc iat

-- | Retrieve the actual virtual parameters for a function call from the context.
-- The argument is the description of the invoked function.
-- The result is a sequence of parameter descriptions of the surrounding function,
-- ordered according to the use in the invoked function.
-- If a virtual parameter is not available, the resulting parameter description has
-- an empty name, a unit type and (only) the required property.
getVirtParamsFromContext :: FuncDesc -> FTrav [ParamDesc]
getVirtParamsFromContext fdes = do
    ctxfdes <- getContextFuncDesc
    let gspdes = map (searchGlobalStateParamDesc ctxfdes) $ getGlobalStateParamProps fdes
    let hupdes = if elem "hu" $ propOfFuncDesc fdes
                    then [searchHeapUseParamDesc ctxfdes]
                    else []
    let vrpdes = case getVariadicParamDesc fdes of
                    Nothing -> []
                    Just pdes -> [pdes]
    return (gspdes ++ hupdes ++ vrpdes)

-- | Determine actual parameters as list of BindsPairs and pattern to bind the result of a function call.
-- The first argument is the variable to reuse for the dunction result
-- The second argument is the description of the invoked function.
-- The third argument is the list of translated C argument expressions.
processParamVals :: TypedVar -> FuncDesc -> [BindsPair] -> FTrav ([BindsPair], GenIrrefPatn)
processParamVals v fdes pvals = do
    -- construct BindsPairs for all virtual parameters
    vpds <- getVirtParamsFromContext fdes
    vpbps <- mapM (\pdes -> do 
                             cnt <- getValCounter
                             return $ mkValVarBindsPair cnt $ getTypedVarFromParamDesc pdes) vpds
    let -- modify types of non-virtual parameters
        nvpbps = map (\(bp, pdes) -> replaceBoundVarType (typeOfParamDesc pdes) bp) $ zip pvals pdess
        -- the list of all actual parameters
        allpbps = nvpbps ++ vpbps
    let -- additional result variables
        arvars = map (lvalVar . fst) $ filter (\(_,pdes) -> isAddResultParam pdes) $ zip allpbps pdess
        -- variable for original function result: for C function with void result use wildcard,
        -- otherwise reuse v
        rvar = if rt == unitType then (TV "_" rt) else (TV (namOfTV v) rt)
        -- pattern for binding the function result
        rpat = mkTuplePattern $ map mkVarPattern (rvar : arvars)
    return (allpbps, rpat)
    where pdess = parsOfFuncDesc fdes
          rt = getResultType $ typeOfFuncDesc fdes

-- | Construct function type from parameter descriptions and result type
-- Comment markers are removed from parameter types used for the result to avoid duplication of comments.
genFunType :: [ParamDesc] -> GenType -> GenType
genFunType pdess rt =
    mkFunType (mkTupleType $ map typeOfParamDesc pdess) $ mkTupleType rtyps
    where rtyps = rt : (map (remComment . typeOfParamDesc) $ filter isAddResultParam pdess)

-- | Construct pattern for formal parameters in function definition.
genFunParamPattern :: FuncDesc -> GenIrrefPatn
genFunParamPattern fdes =
    mkVarTuplePattern $ map getTypedVarFromParamDesc $ parsOfFuncDesc fdes

-- | Construct result expression for function definition.
-- It is a tuple where the first component is the result variable, or unit if the function result type is void.
-- The other components are the additional result parameters.
genFunResultExpr :: FuncDesc -> GenExpr
genFunResultExpr fdes =
    mkExpVarTupleExpr re $ map getTypedVarFromParamDesc $ filter isAddResultParam $ parsOfFuncDesc fdes
    where re = if rt == unitType then mkUnitExpr else mkVarExpr $ TV resVar rt
          rt = getResultType $ typeOfFuncDesc fdes

-- | Construct the item id according to the structure of an expression.
-- This is only needed for encoded function pointer types to determine the
-- correct function type by separately translating the C function type instead of
-- accessing the Cogent function type from the Cogent function pointer type.
getExprItemId :: LC.CExpr -> FTrav String
getExprItemId (LC.CVar nam _) = transObjName nam
getExprItemId (LC.CMember e1 nam arrow _) = do
    iid <- getExprItemId e1
    if null iid
       then return ""
       else if arrow
       then return $ memberSubItemId s $ refSubItemId iid
       else return $ memberSubItemId s iid
    where s = LCI.identToString nam
getExprItemId (LC.CIndex e1 e2 _) = do
    iid <- getExprItemId e1
    if null iid
       then return ""
       else return $ elemSubItemId iid
getExprItemId (LC.CUnary LC.CIndOp e1 _) = do
    iid <- getExprItemId e1
    if null iid
       then return ""
       else return $ refSubItemId iid
getExprItemId (LC.CCall e _ _) = do
    iid <- getExprItemId e
    cft <- exprType e
    if null iid
       then return ""
       else if isFunPointer cft
       then return $ resultSubItemId $ refSubItemId iid
       else return $ resultSubItemId iid
getExprItemId (LC.CAssign _ e1 _ _) = getExprItemId e1
getExprItemId _ = return ""

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
cleanSrc (GenExpr e o t Nothing) = GenExpr (fmap cleanSrc e) o t Nothing
cleanSrc (GenExpr e o t (Just src)) =
    case e of
         CS.App (GenExpr (CS.Var "gencotDummy") _ _ _) _ _ -> GenExpr (fmap cleanSrc e) o t (Just src)
         _ -> GenExpr (fmap cleanSrc e) o t Nothing

{-
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

mkRawExpr :: [RawExpr] -> RawExpr
mkRawExpr [] = CS.RE CS.Unitel
mkRawExpr [re] = re
mkRawExpr res = CS.RE $ CS.Tuple res

setBoxed :: GenType -> GenType
setBoxed (GenType (CS.TCon nam p _) o ms) = (GenType (CS.TCon nam p markBox) o ms)
setBoxed (GenType (CS.TRecord rp fields _) o ms) = (GenType (CS.TRecord rp fields markBox) o ms)
setBoxed (GenType (CS.TUnbox (GenType t _ ms)) o _) = (GenType t o ms)

setUnboxed :: GenType -> GenType
setUnboxed (GenType (CS.TCon nam p _) o ms) = (GenType (CS.TCon nam p markUnbox) o ms)
setUnboxed (GenType (CS.TRecord rp fields _) o ms) = (GenType (CS.TRecord rp fields markUnbox) o ms)
setUnboxed (GenType t o ms) = (GenType (CS.TUnbox (GenType t noOrigin ms)) o Nothing)

markBox = CCT.Boxed False Nothing
markUnbox = CCT.Unboxed

isReadOnly :: GenType -> Bool
isReadOnly (GenType (CS.TBang t) _ _) = True
isReadOnly _ = False

isString :: GenType -> Bool
isString (GenType (CS.TBang t) _ _) = isString t
isString (GenType (CS.TCon "String" _ _) _ _) = True
isString _ = False
-}

setOrigin :: LCN.NodeInfo -> GenType -> GenType
setOrigin n t = (GenType (typeOfGT t) (mkOrigin n) (typSynOfGT t))

remComment :: GenType -> GenType
remComment (GenType t o ms) = GenType t (toNoComOrigin o) ms

errType :: String -> FTrav GenType
errType s = return $ mkTypeName ("err-" ++ s)
