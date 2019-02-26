{-# LANGUAGE PackageImports #-}
module Gencot.C.Translate where

import "language-c" Language.C as LC
import Language.C.Data.Ident as LCI
import Language.C.Data.Node as LCN
import Language.C.Data.Position as LCP
import Language.C.Syntax.AST as LCS

import Control.Applicative ((<*>))
import Data.List (isPrefixOf)
import Data.Foldable (foldrM)
import Numeric (showInt, showOct, showHex, readFloat)

import Gencot.C.Ast as GCA
import Gencot.Origin
import Gencot.Traversal
import Gencot.Names (transTagName,transFunName,transToField,mapNameToUpper,mapNameToLower)

import Language.C.Analysis.TravMonad (getUserState)

checkDeclr :: String -> LC.CDeclr -> OTrav ()
checkDeclr s (LC.CDeclr _ _ Nothing [] _) = return ()
checkDeclr s (LC.CDeclr _ _ _ cattrs n) | not $ null cattrs =
    error $ "Gencot unsupported C: CAttr in " ++ s ++ " at " ++ show n
checkDeclr s (LC.CDeclr _ _ _ _ n) =
    error $ "Gencot unsupported C: asmname in " ++ s ++ " at " ++ show n

retWithOrig :: NodeInfo -> (Origin -> a) -> OTrav a
retWithOrig n gen = do
    o <- getNOrigin n
    return $ gen o

retWithOwnOrig :: OwnOrig -> (Origin -> a) -> OTrav a
retWithOwnOrig oo gen = do
    o <- getOrigin oo
    return $ gen o

retNoOrig :: (Origin -> a) -> OTrav a
retNoOrig gen = return $ gen noOrigin

transUnit :: LC.CTranslUnit -> OTrav [GCA.Definition]
transUnit (CTranslUnit edecls n) = do
    pushOrigs $ map ownOrig edecls
    mapOrigs transExtDecl edecls

transExtDecl :: LC.CExtDecl -> OTrav GCA.Definition
transExtDecl (LC.CDeclExt decl) = do
    pushOrigs [ownOrig decl]
    d <- useOrig transDecl decl
    retWithOrig (nodeInfo decl) $ GCA.DecDef d
transExtDecl (LC.CFDefExt fund) = do 
    pushOrigs [ownOrig fund]
    f <- useOrig transFunDef fund
    retWithOrig (nodeInfo fund) $ GCA.FuncDef f
transExtDecl (LC.CAsmExt (CStrLit (CString asmstr _) _) n) =
    retWithOrig n $ GCA.EscDef ("asm(\"" ++ asmstr ++ "\")")

transFunDef :: LC.CFunDef -> OTrav GCA.Func
transFunDef (LC.CFunDef declspecs dclr _{-old parms-} stat ndef) = do
    checkDeclr "fundef" dclr 
    pushOrigs [lOwnOrig declspecs, ownOrig name, noOwnOrig, ownOrig fdclr, ownOrig stat]
    ds <- useOrig transDeclSpecs declspecs
    i <- useOrig transIdent name
    rd <- useOrig transDerivedDeclrs resdclrs
    ps <- useOrig transParams fdclr
    (GCA.Block bis _) <- useOrig transStat stat
    retWithOrig ndef $ GCA.Func ds i rd ps bis
    where LC.CDeclr (Just name) (fdclr:resdclrs) asmname cattrs ndec = dclr

transStat :: LC.CStat -> OTrav GCA.Stm
transStat (LC.CLabel ident stat cattrs n) = do
    pushOrigs $ [ownOrig ident] ++ (map ownOrig cattrs) ++ [ownOrig stat]
    i <- useOrig transIdent ident
    as <- mapOrigs transAttr cattrs
    s <- useOrig transStat stat
    retWithOrig n $ GCA.Label i as s
transStat (LC.CCase expr stat n) = do
    pushOrigs [ownOrig expr, ownOrig stat]
    e <- useOrig transExpr expr
    s <- useOrig transStat stat
    retWithOrig n $ GCA.Case e s
transStat (LC.CCases expr1 expr2 stat n) =
    error $ "Gencot unsupported C: CCases at " ++ show n
transStat (LC.CDefault stat n) = do
    pushOrigs [ownOrig stat]
    s <- useOrig transStat stat
    retWithOrig n $ GCA.Default s
transStat (LC.CExpr mexpr n) = do
    pushOrigs [mOwnOrig mexpr]
    me <- optOrig transExpr mexpr
    retWithOrig n $ GCA.Exp me
transStat (LC.CCompound _{-localLabels-} bis n) = do
    u1 <- getUserState
    pushOrigs $ map ownOrig bis
    u2 <- getUserState
    error $ "transStat CCompound: u1 = "++(show u1)++" u2 = "++(show u2)
    bs <- mapOrigs transBlockItem bis
    retWithOrig n $ GCA.Block bs
transStat (LC.CIf expr stat mestat n) = do
    pushOrigs [ownOrig expr, ownOrig stat, mOwnOrig mestat]
    e <- useOrig transExpr expr
    s <- useOrig transStat stat
    ms <- optOrig transStat mestat
    retWithOrig n $ GCA.If e s ms
transStat (LC.CSwitch expr stat n) = do
    pushOrigs [ownOrig expr, ownOrig stat]
    e <- useOrig transExpr expr
    s <- useOrig transStat stat
    retWithOrig n $ GCA.Switch e s
transStat (LC.CWhile expr stat False n) = do
    pushOrigs [ownOrig expr, ownOrig stat]
    e <- useOrig transExpr expr
    s <- useOrig transStat stat
    retWithOrig n $ GCA.While e s
transStat (LC.CWhile expr stat True n) = do
    pushOrigs [ownOrig stat, ownOrig expr]
    s <- useOrig transStat stat
    e <- useOrig transExpr expr
    retWithOrig n $ GCA.DoWhile s e
transStat (LC.CFor (Left mexpr) mcond mstep stat n) = do
    pushOrigs [mOwnOrig mexpr, mOwnOrig mcond, mOwnOrig mstep, ownOrig stat]
    me <- optOrig transExpr mexpr
    mc <- optOrig transExpr mcond
    ms <- optOrig transExpr mstep
    s <- useOrig transStat stat
    retWithOrig n $ GCA.For (Right me) mc ms s
transStat (LC.CFor (Right decl) mcond mstep stat n) = do
    pushOrigs [ownOrig decl, mOwnOrig mcond, mOwnOrig mstep, ownOrig stat]
    d <- useOrig transDecl decl
    mc <- optOrig transExpr mcond
    ms <- optOrig transExpr mstep
    s <- useOrig transStat stat
    retWithOrig n $ GCA.For (Left d) mc ms s
transStat (LC.CGoto ident n) = do
    pushOrigs [ownOrig ident]
    i <- useOrig transIdent ident
    retWithOrig n $ GCA.Goto i
transStat (LC.CGotoPtr expr n) =
    error $ "Gencot unsupported C: CGotoPtr at " ++ show n
transStat (LC.CCont n) =
    retWithOrig n $ GCA.Continue
transStat (LC.CBreak n) =
    retWithOrig n $ GCA.Break
transStat (LC.CReturn mexpr n) = do
    pushOrigs [mOwnOrig mexpr]
    me <- optOrig transExpr mexpr
    retWithOrig n $ GCA.Return me
transStat (LC.CAsm asmStmt n) =
    transAsmStmt asmStmt

transAsmStmt :: CAsmStmt -> OTrav GCA.Stm
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

transBlockItem :: LC.CBlockItem -> OTrav GCA.BlockItem
transBlockItem (LC.CBlockStmt stat) = do
    s <- transStat stat
    return $ GCA.BlockStm s
transBlockItem (LC.CBlockDecl decl) = do
    d <- transDecl decl
    return $ GCA.BlockDecl d
transBlockItem (LC.CNestedFunDef fundef) =
    error $ "Gencot unsupported C: CNestedFunDef at " ++ show (LCN.nodeInfo fundef)

transDecl :: LC.CDecl -> OTrav GCA.InitGroup
transDecl (LC.CDecl specs divs n) | any isTypedef stor = do
    pushOrigs $ [noOwnOrig] ++ map (tripOwnOrig mOwnOrig mOwnOrig mOwnOrig) divs
    ss <- useOrig transDeclSpecs specs
    td <- mapOrigs transDeclrToTypedef divs
    retWithOrig n $ GCA.TypedefGroup ss [] td
    where (stor,_,_,_,_,_) = LC.partitionDeclSpecs specs
          isTypedef (LC.CTypedef _) = True
          isTypedef _ = False
          transDeclrToTypedef ((Just dclr@(LC.CDeclr (Just name) _ _ cattrs _)),_,_) = do
              pushOrigs $ [ownOrig name, noOwnOrig] ++ map ownOrig cattrs
              i <- useOrig transIdent name
              d <- useOrig transDeclr dclr
              cs <- mapOrigs transAttr cattrs
              retNoOrig $ GCA.Typedef i d cs
transDecl (LC.CDecl specs divs n) = do
    pushOrigs $ [noOwnOrig] ++ map (tripOwnOrig mOwnOrig mOwnOrig mOwnOrig) divs
    ss <- useOrig transDeclSpecs specs
    it <- mapOrigs transDeclrToInit divs
    retWithOrig n $ GCA.InitGroup ss [] it
    where transDeclrToInit ((Just dclr@(LC.CDeclr (Just name) _ masmname cattrs _)),minit,_) = do
              pushOrigs $ [ownOrig name, noOwnOrig, mOwnOrig masmname, mOwnOrig minit] ++ map ownOrig cattrs
              i <- useOrig transIdent name
              d <- useOrig transDeclr dclr
              ma <- optOrig transStrLit masmname
              mi <- optOrig transInit minit
              cs <- mapOrigs transAttr cattrs
              retNoOrig $ GCA.Init i d ma mi cs
transDecl (LC.CStaticAssert expr str n) =
    error $ "Gencot unsupported C: CStaticAssert at " ++ show n

transMemberDecl :: LC.CDecl -> OTrav GCA.FieldGroup
transMemberDecl (LC.CDecl specs divs n) = do
    pushOrigs $ [noOwnOrig] ++ map (tripOwnOrig mOwnOrig mOwnOrig mOwnOrig) divs
    ss <- useOrig transDeclSpecs specs
    fd <- mapOrigs transDeclrToField divs
    retWithOrig n $ GCA.FieldGroup ss fd
    where 
          transDeclrToField ((Just dclr@(LC.CDeclr mid _ _ cattrs n)),_,mexpr) = do
              --checkDeclr "field" dclr
              pushOrigs [mOwnOrig mid, noOwnOrig, mOwnOrig mexpr]
              mi <- optOrig transIdent mid
              d <- useOrig transDeclr dclr
              me <- optOrig transExpr mexpr
              retNoOrig $ GCA.Field mi (Just d) me
          transDeclrToField (Nothing,_,mexpr) = do
              pushOrigs [mOwnOrig mexpr]
              me <- optOrig transExpr mexpr
              retNoOrig $ GCA.Field Nothing Nothing me
transMemberDecl (LC.CStaticAssert expr str n) =
    error $ "Gencot unsupported C: CStaticAssert at " ++ show n

transParamDecl :: LC.CDecl -> OTrav GCA.Param
transParamDecl (LC.CDecl specs [] n) = do
    pushOrigs [noOwnOrig]
    ss <- useOrig transDeclSpecs specs
    retWithOrig n $ GCA.Param Nothing ss (GCA.DeclRoot noOrigin)
transParamDecl (LC.CDecl specs (((Just dclr@(LC.CDeclr mid _ _ cattrs _)),Nothing,Nothing):[]) n) = do
    checkDeclr "param" dclr
    pushOrigs [noOwnOrig, mOwnOrig mid, noOwnOrig]
    ss <- useOrig transDeclSpecs specs
    mi <- optOrig transIdent mid
    d <- useOrig transDeclr dclr
    retWithOrig n $ GCA.Param mi ss d

transDeclSpecs :: [LC.CDeclSpec] -> OTrav GCA.DeclSpec
transDeclSpecs declspecs = 
    if (not $ null attr) || (not $ null aspc)
       then error $ "Gencot unsupported C: CAttr or CAlignSpec at " ++ (show $ LCN.nodeInfo $ head declspecs)
       else do
           pushOrigs [noOwnOrig, noOwnOrig, noOwnOrig, lOwnOrig spec]
           s <- useOrig (mapM transStorageSpec) stor
           q <- useOrig (mapM transTypeQual) qual
           f <- useOrig (mapM transFunSpec) fspc
           t <- useOrig transTypeSpecs spec
           retNoOrig $ GCA.DeclSpec s (q++f) t
    where (stor,attr,qual,spec,fspc,aspc) = LC.partitionDeclSpecs declspecs

transStorageSpec :: LC.CStorageSpec -> OTrav GCA.Storage
transStorageSpec (LC.CAuto n) = retNoOrig GCA.Tauto
transStorageSpec (LC.CRegister n) = retNoOrig GCA.Tregister
transStorageSpec (LC.CStatic n) = retNoOrig GCA.Tstatic
transStorageSpec (LC.CExtern n) = retNoOrig $ GCA.Textern Nothing
transStorageSpec (LC.CTypedef n) = retNoOrig GCA.Ttypedef
transStorageSpec (LC.CThread n) = 
    error $ "Gencot unsupported C: CThread at " ++ show n

transTypeSpecs :: [LC.CTypeSpec] -> OTrav GCA.TypeSpec
transTypeSpecs ss | (any isVoid ss)    = retNoOrig GCA.Tvoid
transTypeSpecs ss | (any isChar ss)    = retNoOrig $ GCA.Tchar (sign ss)
transTypeSpecs ss | (any isShort ss)   = retNoOrig $ GCA.Tshort (sign ss)
transTypeSpecs ss | (any isComplex ss) = if any isFloat ss
                                         then retNoOrig GCA.Tfloat_Complex
                                         else if any isLong ss
                                             then retNoOrig GCA.Tlong_double_Complex
                                             else retNoOrig GCA.Tdouble_Complex
transTypeSpecs ss | (any isDouble ss)  = if any isLong ss 
                                         then retNoOrig GCA.Tlong_double
                                         else retNoOrig GCA.Tdouble
transTypeSpecs ss | (any isLong ss)    = if hasLongLong ss 
                                         then retNoOrig $ GCA.Tlong_long (sign ss)
                                         else retNoOrig $ GCA.Tlong (sign ss)
transTypeSpecs ss | (any isInt ss)     = retNoOrig $ GCA.Tint (sign ss)
transTypeSpecs ss | (any isSigned ss)  = retNoOrig $ GCA.Tint (sign ss)
transTypeSpecs ss | (any isUnsigned ss)= retNoOrig $ GCA.Tint (sign ss)
transTypeSpecs ss | (any isFloat ss)   = retNoOrig GCA.Tfloat
transTypeSpecs ss | (any isFloatN ss)  = 
    error $ "Gencot unsupported C: CFloatNType at " ++ (show $ LCN.nodeInfo $ head ss)
transTypeSpecs ss | (any isBool ss)    = retNoOrig GCA.T_Bool
transTypeSpecs ss | (any isInt128 ss)  = 
    error $ "Gencot unsupported C: CInt128Type at " ++ (show $ LCN.nodeInfo $ head ss)
transTypeSpecs ((LC.CSUType su n):_)  = transStructUnion su
transTypeSpecs ((LC.CEnumType enum@(LC.CEnum mid menums _ _) n):_) = do
    pushOrigs [mOwnOrig mid, maybeOwnOrig (listOwnOrig (pairOwnOrig ownOrig (mOwnOrig))) menums]
    mi <- optOrig transIdent mid
    es <- useOrig transEnum enum
    retWithOrig n $ GCA.Tenum mi es []
transTypeSpecs ((LC.CTypeDef ident n):_) = do
    pushOrigs [ownOrig ident]
    i <- useOrig transIdent ident
    retNoOrig $ GCA.Tnamed i []
transTypeSpecs ((LC.CTypeOfExpr expr n):_) = do
    pushOrigs [ownOrig expr]
    e <- useOrig transExpr expr
    retNoOrig $ GCA.TtypeofExp e
transTypeSpecs ((LC.CTypeOfType decl n):_) = do
    pushOrigs [ownOrig decl]
    d <- useOrig transDeclToType decl
    retNoOrig $ GCA.TtypeofType d
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

transDeclToType :: LC.CDecl -> OTrav GCA.Type
transDeclToType (LC.CDecl specs [((Just dclr@(LC.CDeclr _ _ _ cattrs ndeclr)),_,_)] n) = do
    checkDeclr "typename" dclr
    pushOrigs [noOwnOrig, noOwnOrig]
    ss <- useOrig transDeclSpecs specs
    d <- useOrig transDeclr dclr
    retWithOrig n $ GCA.Type ss d
transDeclToType (LC.CDecl specs [] n) = do
    pushOrigs [noOwnOrig]
    ss <- useOrig transDeclSpecs specs
    retWithOrig n $ GCA.Type ss (GCA.DeclRoot noOrigin)

transTypeQual :: LC.CTypeQual -> OTrav GCA.TypeQual
transTypeQual (LC.CConstQual n) = retNoOrig GCA.Tconst
transTypeQual (LC.CVolatQual n) = retNoOrig GCA.Tvolatile
transTypeQual (LC.CRestrQual n) = retNoOrig GCA.Trestrict
transTypeQual (LC.CAtomicQual n) = 
    error $ "Gencot unsupported C: CAtomicQual at " ++ show n
transTypeQual (LC.CAttrQual attr)  = do
    pushOrigs [ownOrig attr]
    a <- useOrig transAttr attr
    return $ GCA.TAttr a
transTypeQual (LC.CNullableQual n) =
    error $ "Gencot unsupported C: CNullableQual at " ++ show n
transTypeQual (LC.CNonnullQual n) =
    error $ "Gencot unsupported C: CNonnullQual at " ++ show n

transFunSpec :: LC.CFunSpec -> OTrav GCA.TypeQual
transFunSpec (LC.CInlineQual n) = retNoOrig GCA.Tinline
transFunSpec (LC.CNoreturnQual n) = 
    error $ "Gencot unsupported C: CNoreturnQual at " ++ show n

transStructUnion :: LC.CStructUnion -> OTrav GCA.TypeSpec
transStructUnion (LC.CStruct tag mid mcds cattrs n) = do
    pushOrigs $ (map ownOrig cattrs) ++ [mOwnOrig mid, maybeOwnOrig lOwnOrig mcds]
    cs <- mapOrigs transAttr cattrs
    mi <- optOrig transIdent mid
    mds <- optOrig transMemberDecls mcds
    retWithOrig n $ case tag of 
                        CStructTag -> GCA.Tstruct mi mds cs
                        CUnionTag -> GCA.Tunion mi mds cs
    where transMemberDecls cds = do
            pushOrigs $ map ownOrig cds
            r <- mapOrigs transMemberDecl cds
            return r

transEnum :: LC.CEnum -> OTrav [GCA.CEnum]
transEnum (LC.CEnum _ Nothing _ n) = return []
transEnum (LC.CEnum _ (Just vals) _ n) = do
    pushOrigs $ map (pairOwnOrig ownOrig mOwnOrig) vals
    es <- mapOrigs transEnumerator vals
    return es

transEnumerator :: (LC.Ident,Maybe LC.CExpr) -> OTrav GCA.CEnum
transEnumerator enm@(name, mexpr) = do
    pushOrigs [ownOrig name, mOwnOrig mexpr]
    i <- useOrig transIdent name
    me <- optOrig transExpr mexpr
    retWithOwnOrig (pairOwnOrig ownOrig mOwnOrig enm) $ GCA.CEnum i me

transDeclr :: LC.CDeclr -> OTrav GCA.Decl
transDeclr dclr@(LC.CDeclr _ derived_declrs _ _ n) = transDerivedDeclrs derived_declrs

transDerivedDeclrs :: [LC.CDerivedDeclr] -> OTrav GCA.Decl
transDerivedDeclrs ds = foldrM accdclr (GCA.DeclRoot noOrigin) ds
    where 
        accdclr :: LC.CDerivedDeclr -> GCA.Decl -> OTrav GCA.Decl
        accdclr (LC.CPtrDeclr quals _) dcl = do
            qs <- mapM transTypeQual quals
            retNoOrig $ GCA.Ptr qs dcl
        accdclr (LC.CArrDeclr quals size _) dcl = do
            qs <- mapM transTypeQual quals
            a <- transArrSize size
            retNoOrig $ GCA.Array qs a dcl
        accdclr fd@(LC.CFunDeclr _ _ _ ) dcl = do
            ps <- transParams fd
            retNoOrig $ GCA.Proto dcl ps

transParams :: LC.CDerivedDeclr -> OTrav GCA.Params
transParams (LC.CFunDeclr (Right (decls, isVariadic)) _{-fun_attrs-} n) = do
    pushOrigs $ map ownOrig decls
    ps <- mapOrigs transParamDecl decls
    retNoOrig $ GCA.Params ps isVariadic

transArrSize :: LC.CArrSize -> OTrav GCA.ArraySize
transArrSize (LC.CNoArrSize True) = retNoOrig GCA.VariableArraySize
transArrSize (LC.CNoArrSize False) = retNoOrig GCA.NoArraySize
transArrSize (LC.CArrSize staticMod expr) = do
    pushOrigs [ownOrig expr]
    e <- useOrig transExpr expr
    retNoOrig $ GCA.ArraySize staticMod e

transInit :: LC.CInit -> OTrav GCA.Initializer
transInit (LC.CInitExpr expr n) = do
    pushOrigs [ownOrig expr]
    e <- useOrig transExpr expr
    retWithOrig n $ GCA.ExpInitializer e
transInit (LC.CInitList initl n) = do
    pushOrigs $ map (pairOwnOrig lOwnOrig ownOrig) initl
    is <- mapOrigs transDesig initl
    retWithOrig n $ GCA.CompoundInitializer is

transDesig :: ([LC.CDesignator], LC.CInit) -> OTrav (Maybe GCA.Designation, GCA.Initializer)
transDesig ([],ini) = do
    pushOrigs [ownOrig ini]
    i <- useOrig transInit ini
    return (Nothing,i)
transDesig (desigs,ini) = do
    pushOrigs $ (map ownOrig desigs) ++ [ownOrig ini]
    ds <- mapOrigs transDesignator desigs
    i <- useOrig transInit ini
    return (Just (GCA.Designation ds noOrigin),i)

transDesignator :: LC.CDesignator -> OTrav GCA.Designator
transDesignator (LC.CArrDesig expr n) = do
    pushOrigs [ownOrig expr]
    e <- useOrig transExpr expr
    retWithOrig n $ GCA.IndexDesignator e
transDesignator (LC.CMemberDesig ident n) = do
    pushOrigs [ownOrig ident]
    i <- useOrig transIdent ident
    retWithOrig n $ GCA.MemberDesignator i
transDesignator (LC.CRangeDesig expr1 expr2 n) =
    error $ "Gencot unsupported C: CRangeDesig at " ++ show n

transAttr :: LC.CAttr -> OTrav GCA.Attr
transAttr (LC.CAttr attrName attrParams n) = do
    pushOrigs $ [ownOrig attrName] ++ map ownOrig attrParams
    i <- useOrig transIdent attrName
    es <- mapOrigs transExpr attrParams
    retWithOrig n $ GCA.Attr i es

transExpr :: LC.CExpr -> OTrav GCA.Exp
transExpr (LC.CComma [] n) = 
    error $ "Gencot unsupported C: CComma [] at " ++ show n
transExpr (LC.CComma (_:[]) n) =
    error $ "Gencot unsupported C: CComma [expr] at " ++ show n
transExpr (LC.CComma exprs n) = do
    pushOrigs $ map ownOrig exprs
    es <- mapOrigs transExpr exprs
    retWithOrig n $ GCA.Seq (head es) $ foldr1 (\e2 -> (\e1 -> GCA.Seq e1 e2 noOrigin)) $ tail es
transExpr (LC.CAssign op expr1 expr2 n) = do
    pushOrigs [ownOrig expr1, ownOrig expr2]
    e1 <- useOrig transExpr expr1
    e2 <- useOrig transExpr expr2
    retWithOrig n $ GCA.Assign e1 (tAssignOp op) e2
transExpr (LC.CCond expr1 Nothing expr3 n) = 
    error $ "Gencot unsupported C: CCond expr Nothing expr at " ++ show n
transExpr (LC.CCond expr1 (Just expr2) expr3 n) = do
    pushOrigs [ownOrig expr1, ownOrig expr2, ownOrig expr3]
    e1 <- useOrig transExpr expr1
    e2 <- useOrig transExpr expr2
    e3 <- useOrig transExpr expr3
    retWithOrig n $ GCA.Cond e1 e2 e3
transExpr (LC.CBinary op expr1 expr2 n) = do
    pushOrigs [ownOrig expr1, ownOrig expr2]
    e1 <- useOrig transExpr expr1
    e2 <- useOrig transExpr expr2
    retWithOrig n $ GCA.BinOp (tBinaryOp op) e1 e2
transExpr (LC.CCast decl expr n) = do
    pushOrigs [ownOrig decl, ownOrig expr]
    d <- useOrig transDeclToType decl
    e <- useOrig transExpr expr
    retWithOrig n $ GCA.Cast d e
transExpr (LC.CUnary LC.CPreIncOp expr n) = do
    pushOrigs [ownOrig expr]
    e <- useOrig transExpr expr
    retWithOrig n $ GCA.PreInc e
transExpr (LC.CUnary LC.CPreDecOp expr n) = do
    pushOrigs [ownOrig expr]
    e <- useOrig transExpr expr
    retWithOrig n $ GCA.PreDec e
transExpr (LC.CUnary LC.CPostIncOp expr n) = do
    pushOrigs [ownOrig expr]
    e <- useOrig transExpr expr
    retWithOrig n $ GCA.PostInc e
transExpr (LC.CUnary LC.CPostDecOp expr n) = do
    pushOrigs [ownOrig expr]
    e <- useOrig transExpr expr
    retWithOrig n $ GCA.PostDec e
transExpr (LC.CUnary op expr n) = do
    pushOrigs [ownOrig expr]
    e <- useOrig transExpr expr
    retWithOrig n $ GCA.UnOp (tUnaryOp op) e
transExpr (LC.CSizeofExpr expr n) = do
    pushOrigs [ownOrig expr]
    e <- useOrig transExpr expr
    retWithOrig n $ GCA.SizeofExp e
transExpr (LC.CSizeofType decl n) = do
    pushOrigs [ownOrig decl]
    d <- useOrig transDeclToType decl
    retWithOrig n $ GCA.SizeofType d
transExpr (LC.CAlignofExpr expr n) =
    error $ "Gencot unsupported C: CAlignofExpr at " ++ show n
transExpr (LC.CAlignofType decl n) =
    error $ "Gencot unsupported C: CAlignofType at " ++ show n
transExpr (LC.CComplexReal expr n) =
    error $ "Gencot unsupported C: CComplexReal at " ++ show n
transExpr (LC.CComplexImag expr n) =
    error $ "Gencot unsupported C: CComplexImag at " ++ show n
transExpr (LC.CIndex expr1 expr2 n) = do
    pushOrigs [ownOrig expr1, ownOrig expr2]
    e1 <- useOrig transExpr expr1
    e2 <- useOrig transExpr expr2
    retWithOrig n $ GCA.Index e1 e2
transExpr (LC.CCall expr args n) = do
    pushOrigs $ [ownOrig expr] ++ map ownOrig args
    e <- useOrig transExpr expr
    as <- mapOrigs transExpr args
    retWithOrig n $ GCA.FnCall e as
transExpr (LC.CMember expr ident isPtr n) = do
    pushOrigs [ownOrig expr, ownOrig ident]
    e <- useOrig transExpr expr
    i <- useOrig transIdent ident
    retWithOrig n $ (if isPtr then GCA.PtrMember else GCA.Member) e i
transExpr (LC.CVar ident n) = do
    pushOrigs [ownOrig ident]
    i <- useOrig transIdent ident
    retWithOrig n $ GCA.Var i
transExpr (LC.CConst constant) = do
    pushOrigs [ownOrig constant]
    c <- useOrig transConst constant
    retNoOrig $ GCA.Const c
transExpr (LC.CCompoundLit decl initl n) = do
    pushOrigs $ [ownOrig decl] ++ map (pairOwnOrig lOwnOrig ownOrig) initl
    d <- useOrig transDeclToType decl
    is <- mapOrigs transDesig initl
    retWithOrig n $ GCA.CompoundLit d is
transExpr (LC.CStatExpr (LC.CCompound _{-localLabels-} blockitems nstat) nexpr) = do
    pushOrigs $ map ownOrig blockitems
    bis <- mapOrigs transBlockItem blockitems
    retWithOrig nexpr $ GCA.StmExpr bis -- is GCA.StmExpr correct here?
transExpr (LC.CStatExpr stat n) = do
    pushOrigs [ownOrig stat]
    s <- useOrig transStat stat
    retWithOrig n $ GCA.StmExpr [GCA.BlockStm s]
transExpr (LC.CLabAddrExpr ident n) = 
    error $ "Gencot unsupported C: CLabAddrExpr at " ++ show n
transExpr (LC.CGenericSelection expr assoc_list n) =
    error $ "Gencot unsupported C: CGenericSelection at " ++ show n
transExpr (LC.CBuiltinExpr builtin) = transBuiltin builtin

transBuiltin :: LC.CBuiltin -> OTrav GCA.Exp
transBuiltin (LC.CBuiltinVaArg expr ty_name n) = do
    pushOrigs [ownOrig expr, ownOrig ty_name]
    e <- useOrig transExpr expr
    d <- useOrig transDeclToType ty_name
    retWithOrig n $ GCA.BuiltinVaArg e d
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

transConst :: LC.CConst -> OTrav GCA.Const
transConst (LC.CIntConst   (LC.CInteger i rep flags) n) =
    if LC.testFlag LC.FlagLongLong flags
       then retNoOrig $ GCA.LongLongIntConst (raw rep i) (signed flags) i
       else if LC.testFlag LC.FlagLong flags
            then retNoOrig $ GCA.LongIntConst (raw rep i) (signed flags) i
            else retNoOrig $ GCA.IntConst (raw rep i) (signed flags) i
transConst (LC.CCharConst  (LC.CChar chr wd) n) = 
    retNoOrig $ GCA.CharConst (prewd wd $ LC.showCharConst chr "") chr
{- Multicharacter char constants cannot be fully represented in language-c-quote,
   since GCA.CharConst uses a single Haskell char. 
   We generate only the raw representation and set the actual representation to ' '. 
   This is sufficient for prettyprinting. -}
transConst (LC.CCharConst  (LC.CChars chrs wd) n) = 
    retNoOrig $ GCA.CharConst (prewd wd ("'"++(init $ tail $ LC.showStringLit chrs "")++"'")) ' '
{- Float constants are only represented in their raw form in language-c.
   Therefore we only transfer the raw representation to language-c-quote and set the actual float to 1.0.
   This is sufficient for prettyprinting, since language-c always generates positive float constants
   and language-c-quote uses only the sign of the actual representation for operator precedence. -}
transConst (LC.CFloatConst (LC.CFloat str) n) = 
    retNoOrig $ GCA.FloatConst str 1.0
{- Sequences of String literals are concatenated by language-c.
   Therefore we cannot transfer the original sequence to language-c-quote.
   The prettyprinter directly uses the raw representation, therefore we only generate that. -}
transConst (LC.CStrConst   (LC.CString str wd) n) = 
    retNoOrig $ GCA.StringConst [prewd wd $ LC.showStringLit str ""] ""

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

transStrLit :: LC.CStrLit -> OTrav GCA.StringLit
transStrLit (LC.CStrLit (LC.CString str wd) n) = 
    retWithOrig n $ GCA.StringLit [prewd wd $ LC.showStringLit str ""] ""

transIdent :: LCI.Ident -> OTrav GCA.Id
transIdent (LCI.Ident name _ n) = retWithOrig n $ GCA.Id name
