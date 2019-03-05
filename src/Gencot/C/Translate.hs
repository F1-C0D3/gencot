{-# LANGUAGE PackageImports #-}
module Gencot.C.Translate where

import "language-c" Language.C as LC
import Language.C.Data.Ident as LCI
import Language.C.Data.Node as LCN
import Language.C.Data.Position as LCP
import Language.C.Syntax.AST as LCS

import Control.Applicative (liftA2)
import Data.List (isPrefixOf)
import Data.Foldable (foldrM)
import Numeric (showInt, showOct, showHex, readFloat)

import Gencot.C.Ast as GCA
import Gencot.Origin (Origin,noOrigin,origin,mkOrigin,listOrigin,pairOrigin,maybeOrigin)
import Gencot.Names (transTagName,transObjName,srcFileName,mapObjectName,mapIfUpper,mapNameToUpper,mapNameToLower)
import Gencot.Traversal (FTrav)

import Language.C.Analysis.TravMonad (MonadTrav)
import qualified Language.C.Analysis as LCA

checkDeclr :: String -> LC.CDeclr -> FTrav ()
checkDeclr s (LC.CDeclr _ _ Nothing [] _) = return ()
checkDeclr s (LC.CDeclr _ _ _ cattrs n) | not $ null cattrs =
    error $ "Gencot unsupported C: CAttr in " ++ s ++ " at " ++ show n
checkDeclr s (LC.CDeclr _ _ _ _ n) =
    error $ "Gencot unsupported C: asmname in " ++ s ++ " at " ++ show n

transUnit :: LC.CTranslUnit -> FTrav [GCA.Definition]
transUnit (CTranslUnit edecls n) =
    mapM transExtDecl edecls

transExtDecl :: LC.CExtDecl -> FTrav GCA.Definition
transExtDecl (LC.CDeclExt decl) = do
    d <- transDecl decl
    return $ GCA.DecDef d noOrigin
transExtDecl (LC.CFDefExt fund) = do 
    f <- transFunDef fund
    return $ GCA.FuncDef f noOrigin
transExtDecl (LC.CAsmExt (CStrLit (CString asmstr _) _) n) =
    return $ GCA.EscDef ("asm(\"" ++ asmstr ++ "\")") $ mkOrigin n

transFunDef :: LC.CFunDef -> FTrav GCA.Func
transFunDef (LC.CFunDef declspecs dclr _{-old parms-} stat ndef) = do
    checkDeclr "fundef" dclr 
    ds <- transDeclSpecs declspecs
    fnam <- srcFileName ndef
    rd <- transDerivedDeclrs resdclrs
    ps <- transParams fdclr
    (GCA.Block bis _) <- transStat stat
    return $ GCA.Func ds (mkMapId (const $ mapObjectName name lnk fnam) name) rd ps bis $ mkOrigin ndef
    where LC.CDeclr (Just name) (fdclr:resdclrs) asmname cattrs ndec = dclr
          lnk = if any isIntern declspecs then LCA.InternalLinkage else LCA.ExternalLinkage
          isIntern (CStorageSpec (CStatic _)) = True
          isIntern _ = False

transStat :: LC.CStat -> FTrav GCA.Stm
transStat (LC.CLabel ident stat cattrs n) = do
    as <- mapM transAttr cattrs
    s <- transStat stat
    return $ GCA.Label (mkId ident) as s $ mkOrigin n
transStat (LC.CCase expr stat n) = do
    e <- transExpr expr
    s <- transStat stat
    return $ GCA.Case e s $ mkOrigin n
transStat (LC.CCases expr1 expr2 stat n) =
    error $ "Gencot unsupported C: CCases at " ++ show n
transStat (LC.CDefault stat n) = do
    s <- transStat stat
    return $ GCA.Default s $ mkOrigin n
transStat (LC.CExpr mexpr n) = do
    me <- mapM transExpr mexpr
    return $ GCA.Exp me $ mkOrigin n
transStat (LC.CCompound _{-localLabels-} bis n) = do
    LCA.enterBlockScope
    bs <- mapM transBlockItem bis
    LCA.leaveBlockScope
    return $ GCA.Block bs $ mkOrigin n
transStat (LC.CIf expr stat mestat n) = do
    e <- transExpr expr
    s <- transStat stat
    ms <- mapM transStat mestat
    return $ GCA.If e s ms $ mkOrigin n
transStat (LC.CSwitch expr stat n) = do
    e <- transExpr expr
    s <- transStat stat
    return $ GCA.Switch e s $ mkOrigin n
transStat (LC.CWhile expr stat False n) = do
    e <- transExpr expr
    s <- transStat stat
    return $ GCA.While e s $ mkOrigin n
transStat (LC.CWhile expr stat True n) = do
    s <- transStat stat
    e <- transExpr expr
    return $ GCA.DoWhile s e $ mkOrigin n
transStat (LC.CFor (Left mexpr) mcond mstep stat n) = do
    LCA.enterBlockScope
    me <- mapM transExpr mexpr
    mc <- mapM transExpr mcond
    ms <- mapM transExpr mstep
    s <- transStat stat
    LCA.leaveBlockScope
    return $ GCA.For (Right me) mc ms s $ mkOrigin n
transStat (LC.CFor (Right decl) mcond mstep stat n) = do
    LCA.enterBlockScope
    d <- transDecl decl
    mc <- mapM transExpr mcond
    ms <- mapM transExpr mstep
    s <- transStat stat
    LCA.leaveBlockScope
    return $ GCA.For (Left d) mc ms s $ mkOrigin n
transStat (LC.CGoto ident n) = 
    return $ GCA.Goto (mkId ident) $ mkOrigin n
transStat (LC.CGotoPtr expr n) =
    error $ "Gencot unsupported C: CGotoPtr at " ++ show n
transStat (LC.CCont n) =
    return $ GCA.Continue $ mkOrigin n
transStat (LC.CBreak n) =
    return $ GCA.Break $ mkOrigin n
transStat (LC.CReturn mexpr n) = do
    me <- mapM transExpr mexpr
    return $ GCA.Return me $ mkOrigin n
transStat (LC.CAsm asmStmt n) =
    transAsmStmt asmStmt

transAsmStmt :: CAsmStmt -> FTrav GCA.Stm
transAsmStmt (LC.CAsmStmt tyQual expr outOps inOps clobbers n) =
    error $ "Gencot unsupported C: CAsmStmt at " ++ show n
    {-
       GCA.Asm Bool [Attr] AsmTemplate [AsmOut] [AsmIn] [AsmClobber] noOrigin
       GCA.AsmGoto Bool [Attr] AsmTemplate [AsmIn] [AsmClobber] [Id] noOrigin
    -}

{-
transAsmOperand :: CAsmOperand -> ??
    -- asm_operand :~ [operand-name] "constraint" ( expr )
transAsmOperand (LC.CAsmOperand mArgName cnstr expr n) =
-}

transBlockItem :: LC.CBlockItem -> FTrav GCA.BlockItem
transBlockItem (LC.CBlockStmt stat) = do
    s <- transStat stat
    return $ GCA.BlockStm s
transBlockItem (LC.CBlockDecl decl) = do
    LCA.analyseDecl True decl
    d <- transDecl decl
    return $ GCA.BlockDecl d
transBlockItem (LC.CNestedFunDef fundef) =
    error $ "Gencot unsupported C: CNestedFunDef at " ++ show (LCN.nodeInfo fundef)

transDecl :: LC.CDecl -> FTrav GCA.InitGroup
transDecl (LC.CDecl specs divs n) | any isTypedef stor = do
    ss <- transDeclSpecs specs
    td <- mapM transDeclrToTypedef divs
    return $ GCA.TypedefGroup ss [] td $ mkOrigin n
    where (stor,_,_,_,_,_) = LC.partitionDeclSpecs specs
          isTypedef (LC.CTypedef _) = True
          isTypedef _ = False
          transDeclrToTypedef ((Just dclr@(LC.CDeclr (Just name) _ _ cattrs _)),_,_) = do
              d <- transDeclr dclr
              cs <- mapM transAttr cattrs
              return $ GCA.Typedef (mkMapId mapNameToUpper name) d cs noOrigin
transDecl (LC.CDecl specs divs n) = do
    ss <- transDeclSpecs specs
    it <- mapM transDeclrToInit divs
    return $ GCA.InitGroup ss [] it $ mkOrigin n
    where transDeclrToInit ((Just dclr@(LC.CDeclr (Just name) _ masmname cattrs _)),minit,_) = do
              i <- transObjName name
              d <- transDeclr dclr
              ma <- mapM transStrLit masmname
              mi <- mapM transInit minit
              cs <- mapM transAttr cattrs
              return $ GCA.Init (mkMapId (const i) name) d ma mi cs noOrigin
transDecl (LC.CStaticAssert expr str n) =
    error $ "Gencot unsupported C: CStaticAssert at " ++ show n

transMemberDecl :: LC.CDecl -> FTrav GCA.FieldGroup
transMemberDecl (LC.CDecl specs divs n) = do
    ss <- transDeclSpecs specs
    fd <- mapM transDeclrToField divs
    return $ GCA.FieldGroup ss fd $ mkOrigin n
    where 
          transDeclrToField ((Just dclr@(LC.CDeclr mid _ _ cattrs n)),_,mexpr) = do
              --checkDeclr "field" dclr
              d <- transDeclr dclr
              me <- mapM transExpr mexpr
              return $ GCA.Field (fmap (mkMapId mapIfUpper) mid) (Just d) me noOrigin
          transDeclrToField (Nothing,_,mexpr) = do
              me <- mapM transExpr mexpr
              return $ GCA.Field Nothing Nothing me noOrigin
transMemberDecl (LC.CStaticAssert expr str n) =
    error $ "Gencot unsupported C: CStaticAssert at " ++ show n

transParamDecl :: LC.CDecl -> FTrav GCA.Param
transParamDecl (LC.CDecl specs [] n) = do
    ss <- transDeclSpecs specs
    return $ GCA.Param Nothing ss (GCA.DeclRoot noOrigin) $ mkOrigin n
transParamDecl (LC.CDecl specs (((Just dclr@(LC.CDeclr mid _ _ cattrs _)),Nothing,Nothing):[]) n) = do
    checkDeclr "param" dclr
    ss <- transDeclSpecs specs
    d <- transDeclr dclr
    return $ GCA.Param (fmap (mkMapId mapIfUpper) mid) ss d $ mkOrigin n

transDeclSpecs :: [LC.CDeclSpec] -> FTrav GCA.DeclSpec
transDeclSpecs declspecs = 
    if (not $ null attr) || (not $ null aspc)
       then error $ "Gencot unsupported C: CAttr or CAlignSpec at " ++ (show $ LCN.nodeInfo $ head declspecs)
       else do
           s <- (mapM transStorageSpec) stor
           q <- (mapM transTypeQual) qual
           f <- (mapM transFunSpec) fspc
           t <- transTypeSpecs spec
           return $ GCA.DeclSpec s (q++f) t noOrigin
    where (stor,attr,qual,spec,fspc,aspc) = LC.partitionDeclSpecs declspecs

transStorageSpec :: LC.CStorageSpec -> FTrav GCA.Storage
transStorageSpec (LC.CAuto n) = return $ GCA.Tauto $ mkOrigin n
transStorageSpec (LC.CRegister n) = return $ GCA.Tregister $ mkOrigin n
transStorageSpec (LC.CStatic n) = return $ GCA.Tstatic $ mkOrigin n
transStorageSpec (LC.CExtern n) = return $ GCA.Textern Nothing $ mkOrigin n
transStorageSpec (LC.CTypedef n) = return $ GCA.Ttypedef $ mkOrigin n
transStorageSpec (LC.CThread n) = 
    error $ "Gencot unsupported C: CThread at " ++ show n

transTypeSpecs :: [LC.CTypeSpec] -> FTrav GCA.TypeSpec
transTypeSpecs ss | (any isVoid ss)    = return $ GCA.Tvoid noOrigin
transTypeSpecs ss | (any isChar ss)    = return $ mkTypeName ss "U8"
transTypeSpecs ss | (any isShort ss)   = return $ mkTypeName ss "U16"
transTypeSpecs ss | (any isComplex ss) = return $ mkTypeName ss "err-complex"
transTypeSpecs ss | (any isDouble ss)  = return $ mkTypeName ss "err-float"
transTypeSpecs ss | (any isLong ss)    = return $ mkTypeName ss "U64"
transTypeSpecs ss | (any isInt ss)     = return $ mkTypeName ss "U32"
transTypeSpecs ss | (any isSigned ss)  = return $ mkTypeName ss "U32"
transTypeSpecs ss | (any isUnsigned ss)= return $ mkTypeName ss "U32"
transTypeSpecs ss | (any isFloat ss)   = return $ mkTypeName ss "err-float"
transTypeSpecs ss | (any isFloatN ss)  = 
    error $ "Gencot unsupported C: CFloatNType at " ++ (show $ LCN.nodeInfo $ head ss)
transTypeSpecs ss | (any isBool ss)    = return $ mkTypeName ss "todo-bool"
transTypeSpecs ss | (any isInt128 ss)  = 
    error $ "Gencot unsupported C: CInt128Type at " ++ (show $ LCN.nodeInfo $ head ss)
transTypeSpecs ((LC.CSUType su n):_)  = transStructUnion su
transTypeSpecs ((LC.CEnumType enum@(LC.CEnum mid menums _ _) n):_) = do
    mi <- mapM (transTagName . mkEnumTagName) mid
    es <- transEnum enum
    return $ GCA.Tenum (mId mi mid) es [] $ mkOrigin n
transTypeSpecs ss@((LC.CTypeDef ident n):_) = do
    t <- LCA.lookupTypeDef ident
    let ub = if isAggregate $ resolveTypedef t then "#" else ""
    return $ GCA.Tnamed (mkMapId ((ub ++) . mapNameToUpper) ident) [] $ listOrigin origin ss
transTypeSpecs ss@((LC.CTypeOfExpr expr n):_) = do
    e <- transExpr expr
    return $ GCA.TtypeofExp e $ listOrigin origin ss
transTypeSpecs ss@((LC.CTypeOfType decl n):_) = do
    d <- transDeclToType decl
    return $ GCA.TtypeofType d $ listOrigin origin ss
transTypeSpecs ss | (any isAtomic ss)  = 
    error $ "Gencot unsupported C: CAtomicType at " ++ (show $ LCN.nodeInfo $ head ss)

sign ss = if any isSigned ss then (Just $ Tsigned noOrigin)
                             else if any isUnsigned ss then (Just $ Tunsigned noOrigin)
                                                       else Nothing
isVoid (LC.CVoidType _)         = True
isVoid _     = False
isChar (LC.CCharType _)         = True
isChar _     = False
isShort (LC.CShortType _)       = True
isShort _    = False
isInt (LC.CIntType _)           = True
isInt _      = False
isLong (LC.CLongType _)         = True
isLong _     = False
isFloat (LC.CFloatType _)       = True
isFloat _    = False
isFloatN (LC.CFloatNType _ _ _) = True
isFloatN _   = False
isDouble (LC.CDoubleType _)     = True
isDouble _   = False
isSigned (LC.CSignedType _)     = True
isSigned _   = False
isUnsigned (LC.CUnsigType _)    = True
isUnsigned _ = False
isBool (LC.CBoolType _)         = True
isBool _     = False
isComplex (LC.CComplexType _)   = True
isComplex _  = False
isInt128 (LC.CInt128Type _)     = True
isInt128 _   = False
isAtomic (LC.CAtomicType _ _)   = True
isAtomic _   = False
hasLongLong ss = (length (filter isLong ss)) > 1

transDeclToType :: LC.CDecl -> FTrav GCA.Type
transDeclToType (LC.CDecl specs [((Just dclr@(LC.CDeclr _ _ _ cattrs ndeclr)),_,_)] n) = do
    checkDeclr "typename" dclr
    ss <- transDeclSpecs specs
    d <- transDeclr dclr
    return $ GCA.Type ss d $ mkOrigin n
transDeclToType (LC.CDecl specs [] n) = do
    ss <- transDeclSpecs specs
    return $ GCA.Type ss (GCA.DeclRoot noOrigin) $ mkOrigin n

transTypeQual :: LC.CTypeQual -> FTrav GCA.TypeQual
transTypeQual (LC.CConstQual n) = return $ GCA.Tconst noOrigin
transTypeQual (LC.CVolatQual n) = return $ GCA.Tvolatile noOrigin
transTypeQual (LC.CRestrQual n) = return $ GCA.Trestrict noOrigin
transTypeQual (LC.CAtomicQual n) = 
    error $ "Gencot unsupported C: CAtomicQual at " ++ show n
transTypeQual (LC.CAttrQual attr)  = do
    a <- transAttr attr
    return $ GCA.TAttr a noOrigin
transTypeQual (LC.CNullableQual n) =
    error $ "Gencot unsupported C: CNullableQual at " ++ show n
transTypeQual (LC.CNonnullQual n) =
    error $ "Gencot unsupported C: CNonnullQual at " ++ show n

transFunSpec :: LC.CFunSpec -> FTrav GCA.TypeQual
transFunSpec (LC.CInlineQual n) = return $ GCA.Tinline noOrigin
transFunSpec (LC.CNoreturnQual n) = 
    error $ "Gencot unsupported C: CNoreturnQual at " ++ show n

transStructUnion :: LC.CStructUnion -> FTrav GCA.TypeSpec
transStructUnion (LC.CStruct tag mid mcds cattrs n) = do
    cs <- mapM transAttr cattrs
    mi <- mapM (transTagName . (mkCompTagName tag)) mid
    mds <- mapM (mapM transMemberDecl) mcds
    return $ case tag of 
                        CStructTag -> GCA.Tstruct (mId mi mid) mds cs $ mkOrigin n
                        CUnionTag -> GCA.Tunion (mId mi mid) mds cs $ mkOrigin n

transEnum :: LC.CEnum -> FTrav [GCA.CEnum]
transEnum (LC.CEnum _ Nothing _ n) = return []
transEnum (LC.CEnum _ (Just vals) _ n) =
    mapM transEnumerator vals

transEnumerator :: (LC.Ident,Maybe LC.CExpr) -> FTrav GCA.CEnum
transEnumerator enm@(name, mexpr) = do
    me <- mapM transExpr mexpr
    return $ GCA.CEnum (mkMapId mapNameToLower name) me $ pairOrigin origin (maybeOrigin origin) enm

transDeclr :: LC.CDeclr -> FTrav GCA.Decl
transDeclr dclr@(LC.CDeclr _ derived_declrs _ _ n) = transDerivedDeclrs derived_declrs

transDerivedDeclrs :: [LC.CDerivedDeclr] -> FTrav GCA.Decl
transDerivedDeclrs ds = foldrM accdclr (GCA.DeclRoot noOrigin) ds
    where 
        accdclr :: LC.CDerivedDeclr -> GCA.Decl -> FTrav GCA.Decl
        accdclr (LC.CPtrDeclr quals _) dcl = do
            qs <- mapM transTypeQual quals
            return $ GCA.Ptr qs dcl noOrigin
        accdclr (LC.CArrDeclr quals size _) dcl = do
            qs <- mapM transTypeQual quals
            a <- transArrSize size
            return $ GCA.Array qs a dcl noOrigin
        accdclr fd@(LC.CFunDeclr _ _ _ ) dcl = do
            ps <- transParams fd
            return $ GCA.Proto dcl ps noOrigin

transParams :: LC.CDerivedDeclr -> FTrav GCA.Params
transParams (LC.CFunDeclr (Right (decls, isVariadic)) _{-fun_attrs-} n) = do
    ps <- mapM transParamDecl decls
    return $ GCA.Params ps isVariadic noOrigin

transArrSize :: LC.CArrSize -> FTrav GCA.ArraySize
transArrSize (LC.CNoArrSize True) = return $ GCA.VariableArraySize noOrigin
transArrSize (LC.CNoArrSize False) = return $ GCA.NoArraySize noOrigin
transArrSize (LC.CArrSize staticMod expr) = do
    e <- transExpr expr
    return $ GCA.ArraySize staticMod e noOrigin

transInit :: LC.CInit -> FTrav GCA.Initializer
transInit (LC.CInitExpr expr n) = do
    e <- transExpr expr
    return $ GCA.ExpInitializer e $ mkOrigin n
transInit (LC.CInitList initl n) = do
    is <- mapM transDesig initl
    return $ GCA.CompoundInitializer is $ mkOrigin n

transDesig :: ([LC.CDesignator], LC.CInit) -> FTrav (Maybe GCA.Designation, GCA.Initializer)
transDesig ([],ini) = do
    i <- transInit ini
    return (Nothing,i)
transDesig (desigs,ini) = do
    ds <- mapM transDesignator desigs
    i <- transInit ini
    return (Just (GCA.Designation ds noOrigin),i)

transDesignator :: LC.CDesignator -> FTrav GCA.Designator
transDesignator (LC.CArrDesig expr n) = do
    e <- transExpr expr
    return $ GCA.IndexDesignator e $ mkOrigin n
transDesignator (LC.CMemberDesig ident n) = do
    return $ GCA.MemberDesignator (mkMapId mapIfUpper ident) $ mkOrigin n
transDesignator (LC.CRangeDesig expr1 expr2 n) =
    error $ "Gencot unsupported C: CRangeDesig at " ++ show n

transAttr :: LC.CAttr -> FTrav GCA.Attr
transAttr (LC.CAttr attrName attrParams n) = do
    es <- mapM transExpr attrParams
    return $ GCA.Attr (mkId attrName) es $ mkOrigin n

transExpr :: LC.CExpr -> FTrav GCA.Exp
transExpr (LC.CComma [] n) = 
    error $ "Gencot unsupported C: CComma [] at " ++ show n
transExpr (LC.CComma (_:[]) n) =
    error $ "Gencot unsupported C: CComma [expr] at " ++ show n
transExpr (LC.CComma exprs n) = do
    es <- mapM transExpr exprs
    return $ GCA.Seq (head es) (foldr1 (\e2 -> (\e1 -> GCA.Seq e1 e2 noOrigin)) $ tail es) $ mkOrigin n
transExpr (LC.CAssign op expr1 expr2 n) = do
    e1 <- transExpr expr1
    e2 <- transExpr expr2
    return $ GCA.Assign e1 (tAssignOp op) e2 $ mkOrigin n
transExpr (LC.CCond expr1 Nothing expr3 n) = 
    error $ "Gencot unsupported C: CCond expr Nothing expr at " ++ show n
transExpr (LC.CCond expr1 (Just expr2) expr3 n) = do
    e1 <- transExpr expr1
    e2 <- transExpr expr2
    e3 <- transExpr expr3
    return $ GCA.Cond e1 e2 e3 $ mkOrigin n
transExpr (LC.CBinary op expr1 expr2 n) = do
    e1 <- transExpr expr1
    e2 <- transExpr expr2
    return $ GCA.BinOp (tBinaryOp op) e1 e2 $ mkOrigin n
transExpr (LC.CCast decl expr n) = do
    d <- transDeclToType decl
    e <- transExpr expr
    return $ GCA.Cast d e $ mkOrigin n
transExpr (LC.CUnary LC.CPreIncOp expr n) = do
    e <- transExpr expr
    return $ GCA.PreInc e $ mkOrigin n
transExpr (LC.CUnary LC.CPreDecOp expr n) = do
    e <- transExpr expr
    return $ GCA.PreDec e $ mkOrigin n
transExpr (LC.CUnary LC.CPostIncOp expr n) = do
    e <- transExpr expr
    return $ GCA.PostInc e $ mkOrigin n
transExpr (LC.CUnary LC.CPostDecOp expr n) = do
    e <- transExpr expr
    return $ GCA.PostDec e $ mkOrigin n
transExpr (LC.CUnary op expr n) = do
    e <- transExpr expr
    return $ GCA.UnOp (tUnaryOp op) e $ mkOrigin n
transExpr (LC.CSizeofExpr expr n) = do
    e <- transExpr expr
    return $ GCA.SizeofExp e $ mkOrigin n
transExpr (LC.CSizeofType decl n) = do
    d <- transDeclToType decl
    return $ GCA.SizeofType d $ mkOrigin n
transExpr (LC.CAlignofExpr expr n) =
    error $ "Gencot unsupported C: CAlignofExpr at " ++ show n
transExpr (LC.CAlignofType decl n) =
    error $ "Gencot unsupported C: CAlignofType at " ++ show n
transExpr (LC.CComplexReal expr n) =
    error $ "Gencot unsupported C: CComplexReal at " ++ show n
transExpr (LC.CComplexImag expr n) =
    error $ "Gencot unsupported C: CComplexImag at " ++ show n
transExpr (LC.CIndex expr1 expr2 n) = do
    e1 <- transExpr expr1
    e2 <- transExpr expr2
    return $ GCA.Index e1 e2 $ mkOrigin n
transExpr (LC.CCall expr args n) = do
    e <- transExpr expr
    as <- mapM transExpr args
    return $ GCA.FnCall e as $ mkOrigin n
transExpr (LC.CMember expr ident isPtr n) = do
    e <- transExpr expr
    return $ (if isPtr then GCA.PtrMember else GCA.Member) e i $ mkOrigin n
    where i = mkMapId mapIfUpper ident
transExpr (LC.CVar ident n) = do
    i <- transObjName ident
    return $ GCA.Var (mkMapId (const i) ident) $ mkOrigin n
transExpr (LC.CConst constant) = do
    c <- transConst constant
    return $ GCA.Const c noOrigin
transExpr (LC.CCompoundLit decl initl n) = do
    d <- transDeclToType decl
    is <- mapM transDesig initl
    return $ GCA.CompoundLit d is $ mkOrigin n
transExpr (LC.CStatExpr (LC.CCompound _{-localLabels-} blockitems nstat) nexpr) = do
    LCA.enterBlockScope
    bis <- mapM transBlockItem blockitems
    LCA.leaveBlockScope
    return $ GCA.StmExpr bis $ mkOrigin nexpr -- is GCA.StmExpr correct here?
transExpr (LC.CStatExpr stat n) = do
    s <- transStat stat
    return $ GCA.StmExpr [GCA.BlockStm s] $ mkOrigin n
transExpr (LC.CLabAddrExpr ident n) = 
    error $ "Gencot unsupported C: CLabAddrExpr at " ++ show n
transExpr (LC.CGenericSelection expr assoc_list n) =
    error $ "Gencot unsupported C: CGenericSelection at " ++ show n
transExpr (LC.CBuiltinExpr builtin) = transBuiltin builtin

transBuiltin :: LC.CBuiltin -> FTrav GCA.Exp
transBuiltin (LC.CBuiltinVaArg expr ty_name n) = do
    e <- transExpr expr
    d <- transDeclToType ty_name
    return $ GCA.BuiltinVaArg e d $ mkOrigin n
transBuiltin (LC.CBuiltinOffsetOf _ty_name otherDesigs n) =
    error $ "Gencot unsupported C: CBuiltinOffsetOf at " ++ show n
transBuiltin (LC.CBuiltinTypesCompatible ty1 ty2 n) =
    error $ "Gencot unsupported C: CBuiltinTypesCompatible at " ++ show n
transBuiltin (LC.CBuiltinConvertVector expr ty n)  =
    error $ "Gencot unsupported C: CBuiltinConvertVector at " ++ show n

tAssignOp :: LC.CAssignOp -> GCA.AssignOp
tAssignOp op = case op of
    LC.CAssignOp -> GCA.JustAssign
    LC.CMulAssOp -> GCA.MulAssign
    LC.CDivAssOp -> GCA.DivAssign
    LC.CRmdAssOp -> GCA.ModAssign
    LC.CAddAssOp -> GCA.AddAssign
    LC.CSubAssOp -> GCA.SubAssign
    LC.CShlAssOp -> GCA.LshAssign
    LC.CShrAssOp -> GCA.RshAssign
    LC.CAndAssOp -> GCA.AndAssign
    LC.CXorAssOp -> GCA.XorAssign
    LC.COrAssOp  -> GCA.OrAssign

tBinaryOp :: LC.CBinaryOp -> GCA.BinOp
tBinaryOp op = case op of
    LC.CMulOp -> GCA.Mul
    LC.CDivOp -> GCA.Div
    LC.CRmdOp -> GCA.Mod
    LC.CAddOp -> GCA.Add
    LC.CSubOp -> GCA.Sub
    LC.CShlOp -> GCA.Lsh
    LC.CShrOp -> GCA.Rsh
    LC.CLeOp  -> GCA.Lt
    LC.CGrOp  -> GCA.Gt
    LC.CLeqOp -> GCA.Le
    LC.CGeqOp -> GCA.Ge
    LC.CEqOp  -> GCA.Eq
    LC.CNeqOp -> GCA.Ne
    LC.CAndOp -> GCA.And
    LC.CXorOp -> GCA.Xor
    LC.COrOp  -> GCA.Or
    LC.CLndOp -> GCA.Land
    LC.CLorOp -> GCA.Lor

tUnaryOp :: LC.CUnaryOp -> GCA.UnOp
tUnaryOp op = case op of
    LC.CAdrOp     -> GCA.AddrOf
    LC.CIndOp     -> GCA.Deref
    LC.CPlusOp    -> GCA.Positive
    LC.CMinOp     -> GCA.Negate
    LC.CCompOp    -> GCA.Not
    LC.CNegOp     -> GCA.Lnot

transConst :: LC.CConst -> FTrav GCA.Const
transConst (LC.CIntConst   (LC.CInteger i rep flags) n) =
    if LC.testFlag LC.FlagLongLong flags
       then return $ GCA.LongLongIntConst (raw rep i) (signed flags) i noOrigin
       else if LC.testFlag LC.FlagLong flags
            then return $ GCA.LongIntConst (raw rep i) (signed flags) i noOrigin
            else return $ GCA.IntConst (raw rep i) (signed flags) i noOrigin
transConst (LC.CCharConst  (LC.CChar chr wd) n) = 
    return $ GCA.CharConst (prewd wd $ LC.showCharConst chr "") chr noOrigin
{- Multicharacter char constants cannot be fully represented in language-c-quote,
   since GCA.CharConst uses a single Haskell char. 
   We generate only the raw representation and set the actual representation to ' '. 
   This is sufficient for prettyprinting. -}
transConst (LC.CCharConst  (LC.CChars chrs wd) n) = 
    return $ GCA.CharConst (prewd wd ("'"++(init $ tail $ LC.showStringLit chrs "")++"'")) ' ' noOrigin
{- Float constants are only represented in their raw form in language-c.
   Therefore we only transfer the raw representation to language-c-quote and set the actual float to 1.0.
   This is sufficient for prettyprinting, since language-c always generates positive float constants
   and language-c-quote uses only the sign of the actual representation for operator precedence. -}
transConst (LC.CFloatConst (LC.CFloat str) n) = 
    return $ GCA.FloatConst str 1.0 noOrigin
{- Sequences of String literals are concatenated by language-c.
   Therefore we cannot transfer the original sequence to language-c-quote.
   The prettyprinter directly uses the raw representation, therefore we only generate that. -}
transConst (LC.CStrConst   (LC.CString str wd) n) = 
    return $ GCA.StringConst [prewd wd $ LC.showStringLit str ""] "" noOrigin

prewd :: Bool -> String -> String
prewd True s = "L" ++ s
prewd False s = s

{-
GCA.DoubleConst String Double noOrigin
GCA.LongDoubleConst String Double noOrigin
-}

signed flags = if LC.testFlag LC.FlagUnsigned flags 
                  then GCA.Unsigned
                  else GCA.Signed
raw DecRepr i = showInt i ""
raw HexRepr i = (showString "0x" . showHex i) ""
raw OctalRepr i = (showString "0" . showOct i) ""

transStrLit :: LC.CStrLit -> FTrav GCA.StringLit
transStrLit (LC.CStrLit (LC.CString str wd) n) = 
    return $ GCA.StringLit [prewd wd $ LC.showStringLit str ""] "" $ mkOrigin n

mkTypeName :: [LC.CTypeSpec] -> String -> GCA.TypeSpec
mkTypeName ss nam = GCA.Tnamed (GCA.Id nam noOrigin) [] $ listOrigin origin ss

mkCompTagName :: LC.CStructTag -> LCI.Ident -> LCA.TypeName
mkCompTagName tag idnam = (LCA.TyComp (LCA.CompTypeRef (LCI.NamedRef idnam) kind undefNode))
    where kind = case tag of { LC.CStructTag -> LCA.StructTag; LC.CUnionTag -> LCA.UnionTag}

mkEnumTagName :: LCI.Ident -> LCA.TypeName
mkEnumTagName idnam = (LCA.TyEnum (LCA.EnumTypeRef (LCI.NamedRef idnam) undefNode))

resolveTypedef :: LCA.Type -> LCA.Type
resolveTypedef (LCA.TypeDefType (LCA.TypeDefRef _ t _) _ _) = resolveTypedef t
resolveTypedef t = t

isAggregate :: LCA.Type -> Bool
isAggregate (LCA.DirectType (LCA.TyComp _) _ _) = True
isAggregate (LCA.ArrayType _ _ _ _) = True
isAggregate _ = False

mkId :: LCI.Ident -> GCA.Id
mkId = mkMapId identToString

mkMapId :: (LCI.Ident -> String) -> LCI.Ident -> GCA.Id
mkMapId f idnam = GCA.Id (f idnam) $ origin idnam

mId :: (Maybe String) -> (Maybe LCI.Ident) -> (Maybe GCA.Id)
mId ms mo = (liftA2 mkMapId (fmap const ms) mo)

