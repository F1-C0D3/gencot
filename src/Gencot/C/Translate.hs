{-# LANGUAGE PackageImports #-}
module Gencot.C.Translate where

import "language-c" Language.C as LC
import Language.C.Data.Ident as LCI
import Language.C.Data.Node as LCN
import Language.C.Data.Position as LCP
import Language.C.Syntax.AST as LCS

import Control.Applicative ((<*>))
import Data.List (isPrefixOf)
import Numeric (showInt, showOct, showHex, readFloat)

import Gencot.C.Ast as GCA
import Gencot.Origin
import Gencot.Names (transTagName,transFunName,transToField,mapNameToUpper,mapNameToLower)
 
checkDeclr :: String -> LC.CDeclr -> a -> a
checkDeclr s (LC.CDeclr _ _ Nothing [] _) x = x
checkDeclr s (LC.CDeclr _ _ _ cattrs n) x | not $ null cattrs =
    error $ "Gencot unsupported C: CAttr in " ++ s ++ " at " ++ show n
checkDeclr s (LC.CDeclr _ _ _ _ n) x =
    error $ "Gencot unsupported C: asmname in " ++ s ++ " at " ++ show n

transUnit :: LC.CTranslUnit -> [GCA.Definition]
transUnit (CTranslUnit edecls n) = map transExtDecl edecls

transExtDecl :: LC.CExtDecl -> GCA.Definition
transExtDecl (LC.CDeclExt decl) = GCA.DecDef (transDecl noOrigin decl) noOrigin
transExtDecl (LC.CFDefExt fund) = GCA.FuncDef (transFunDef fund) noOrigin
transExtDecl (LC.CAsmExt  (CStrLit (CString asmstr _) _) n) = GCA.EscDef ("asm(\"" ++ asmstr ++ "\")") noOrigin

transFunDef :: LC.CFunDef -> GCA.Func
transFunDef (LC.CFunDef declspecs 
                dclr@(LC.CDeclr (Just name) (fdclr:resdclrs) asmname cattrs ndec) 
                    _{-old parms-} (LC.CCompound _{-loclabels-} blockitems nbody) ndef) = 
    checkDeclr "fundef" dclr
        GCA.Func (transDeclSpecs declspecs) (transIdent noOrigin name) 
                (transDerivedDeclrs resdclrs) (transParams fdclr) 
                (zipWith transBlockItem (subListOrigins ndef blockitems) blockitems) noOrigin

transStat :: Origin -> LC.CStat -> GCA.Stm
transStat o (LC.CLabel ident stat cattrs n) =
    GCA.Label (transIdent oi ident) (map transAttr cattrs) (transStat os stat) o
    where (oi,oas,os) = sub1l1Origins n ident cattrs stat
transStat o (LC.CCase expr stat n) =
    GCA.Case (transExpr oe expr) (transStat os stat) o
    where (oe,os) = sub2Origins n expr stat
transStat o (LC.CCases expr1 expr2 stat n) =
    error $ "Gencot unsupported C: CCases at " ++ show n
transStat o (LC.CDefault stat n) =
    GCA.Default (transSubStat n stat) o
transStat o (LC.CExpr expr n) =
    GCA.Exp (fmap (transSubExpr n) expr) o
transStat o (LC.CCompound _{-localLabels-} bis n) =
    GCA.Block (zipWith transBlockItem (subListOrigins n bis) bis) $ o
transStat o (LC.CIf expr stat Nothing n) =
    GCA.If (transExpr oe expr) (transStat os stat) Nothing o
    where (oe,os) = sub2Origins n expr stat
transStat o (LC.CIf expr stat (Just estat) n) =
    GCA.If (transExpr oe expr) (transStat os stat) (Just $ transStat oes estat) o
    where (oe,os,oes) = sub3Origins n expr stat estat
transStat o (LC.CSwitch expr stat n) =
    GCA.Switch (transExpr oe expr) (transStat os stat) o
    where (oe,os) = sub2Origins n expr stat
transStat o (LC.CWhile expr stat False n) =
    GCA.While (transExpr oe expr) (transStat os stat) o
    where (oe,os) = sub2Origins n expr stat
transStat o (LC.CWhile expr stat True n) =
    GCA.DoWhile (transStat os stat) (transExpr oe expr) o
    where (os,oe) = sub2Origins n stat expr
transStat o (LC.CFor (Left expr) cond step stat n) =
    GCA.For (Right (transExpr <$> moe <*> expr)) (transExpr <$> mocnd <*> cond) (transExpr <$> mostp <*> step) (transStat os stat) o
    where [moe,mocnd,mostp,Just os] = subListMaybeOrigins n [fn expr,fn cond,fn step,fn $ Just stat]
          fn :: CNode a => Maybe a -> Maybe LCN.NodeInfo
          fn = fmap LCN.nodeInfo
transStat o (LC.CFor (Right decl) cond step stat n) =
    GCA.For (Left $ transDecl noOrigin decl) (transExpr <$> mocnd <*> cond) (transExpr <$> mostp <*> step) (transStat os stat) o
    where [mod,mocnd,mostp,Just os] = subListMaybeOrigins n [fn $ Just decl,fn cond,fn step,fn $ Just stat]
          fn :: CNode a => Maybe a -> Maybe LCN.NodeInfo
          fn = fmap LCN.nodeInfo
transStat o (LC.CGoto ident n) =
    GCA.Goto (transSubIdent n ident) o
transStat o (LC.CGotoPtr expr n) =
    error $ "Gencot unsupported C: CGotoPtr at " ++ show n
transStat o (LC.CCont n) =
    GCA.Continue o
transStat o (LC.CBreak n) =
    GCA.Break o
transStat o (LC.CReturn Nothing n) =
    GCA.Return Nothing o
transStat o (LC.CReturn (Just expr) n) =
    GCA.Return (Just $ transSubExpr n expr) o
transStat o (LC.CAsm asmStmt n) =
    transAsmStmt asmStmt

transSubStat :: LCN.NodeInfo -> LC.CStat -> GCA.Stm
transSubStat n stat = transStat (subOrigin n stat) stat

transAsmStmt :: CAsmStmt -> GCA.Stm
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

transBlockItem :: Origin -> LC.CBlockItem -> GCA.BlockItem
transBlockItem o (LC.CBlockStmt stat) = GCA.BlockStm (transStat o stat)
transBlockItem o (LC.CBlockDecl decl) = GCA.BlockDecl (transDecl o decl)
transBlockItem o (LC.CNestedFunDef fundef) =
    error $ "Gencot unsupported C: CNestedFunDef at " ++ show (LCN.nodeInfo fundef)

transDecl :: Origin -> LC.CDecl -> GCA.InitGroup
transDecl o (LC.CDecl specs divs n) =
    if any isTypedef stor
       then GCA.TypedefGroup (transDSpecs [] specs) [] (map transDeclrToTypedef divs) o
       else GCA.InitGroup (transDSpecs stor specs) [] (map transDeclrToInit divs) o
    where (stor,_,_,_,_,_) = LC.partitionDeclSpecs specs
          isTypedef (LC.CTypedef _) = True
          isTypedef _ = False
          transDeclrToTypedef ((Just dclr@(LC.CDeclr (Just name) _ _ cattrs _)),_,_) = 
              GCA.Typedef (transIdent noOrigin name) (transDeclr dclr) (map transAttr cattrs) noOrigin
          transDeclrToInit ((Just dclr@(LC.CDeclr (Just name) _ asmname cattrs _)),minit,_) =
              GCA.Init (transIdent noOrigin name) (transDeclr dclr) (fmap transStrLit asmname) (fmap transInit minit) (map transAttr cattrs) noOrigin
transDecl o (LC.CStaticAssert expr str n) =
    error $ "Gencot unsupported C: CStaticAssert at " ++ show n

transMemberDecl :: LC.CDecl -> GCA.FieldGroup
transMemberDecl (LC.CDecl specs divs n) =
    GCA.FieldGroup (transDeclSpecs specs) (map transDeclrToField divs) noOrigin
    where 
          transDeclrToField ((Just dclr@(LC.CDeclr mid _ _ cattrs n)),_,mexpr) =
              --checkDeclr "field" dclr
                 GCA.Field (fmap (transIdent noOrigin) mid) (Just $ transDeclr dclr) (fmap (transExpr noOrigin) mexpr) noOrigin
          transDeclrToField (Nothing,_,mexpr) =
              GCA.Field Nothing Nothing (fmap (transExpr noOrigin) mexpr) noOrigin
transMemberDecl (LC.CStaticAssert expr str n) =
    error $ "Gencot unsupported C: CStaticAssert at " ++ show n

transParamDecl :: LC.CDecl -> GCA.Param
transParamDecl (LC.CDecl specs [] n) =
    GCA.Param Nothing (transDeclSpecs specs) (GCA.DeclRoot noOrigin) noOrigin
transParamDecl (LC.CDecl specs (((Just dclr@(LC.CDeclr mid _ _ cattrs _)),Nothing,Nothing):[]) n) =
    checkDeclr "param" dclr
       GCA.Param (fmap (transIdent noOrigin) mid) (transDeclSpecs specs) (transDeclr dclr) noOrigin

transDeclSpecs :: [LC.CDeclSpec] -> GCA.DeclSpec
transDeclSpecs declspecs = transDSpecs stor declspecs
    where (stor,_,_,_,_,_) = LC.partitionDeclSpecs declspecs

transDSpecs :: [LC.CStorageSpec] -> [LC.CDeclSpec] -> GCA.DeclSpec
transDSpecs storspecs declspecs = 
    if (not $ null attr) || (not $ null aspc)
       then error $ "Gencot unsupported C: CAttr or CAlignSpec at " ++ (show $ LCN.nodeInfo $ head declspecs)
       else GCA.DeclSpec (map transStorageSpec storspecs) 
                ((map transTypeQual qual)++(map transFunSpec fspc))
                (transTypeSpecs spec) noOrigin
    where (_,attr,qual,spec,fspc,aspc) = LC.partitionDeclSpecs declspecs

{-
instance Pretty CDeclSpec where
    pretty (LC.CStorageSpec sp) = pretty sp
    pretty (LC.CTypeSpec sp) = pretty sp
    pretty (LC.CTypeQual qu) = pretty qu
    pretty (LC.CFunSpec fs) = pretty fs
    pretty (LC.CAlignSpec sa) = pretty sa

instance Pretty CAlignSpec where
    pretty (LC.CAlignAsType decl _) =
    pretty (LC.CAlignAsExpr expr _) =
-}
    
transStorageSpec :: LC.CStorageSpec -> GCA.Storage
transStorageSpec (LC.CAuto n) = GCA.Tauto noOrigin
transStorageSpec (LC.CRegister n) = GCA.Tregister noOrigin
transStorageSpec (LC.CStatic n) = GCA.Tstatic noOrigin
transStorageSpec (LC.CExtern n) = GCA.Textern Nothing noOrigin
transStorageSpec (LC.CTypedef n) = GCA.Ttypedef noOrigin
transStorageSpec (LC.CThread n) = 
    error $ "Gencot unsupported C: CThread at " ++ show n

transTypeSpecs :: [LC.CTypeSpec] -> GCA.TypeSpec
transTypeSpecs ss | (any isVoid ss)    = GCA.Tvoid noOrigin
transTypeSpecs ss | (any isChar ss)    = GCA.Tchar (sign ss) noOrigin
transTypeSpecs ss | (any isShort ss)   = GCA.Tshort (sign ss) noOrigin
transTypeSpecs ss | (any isComplex ss) = if any isFloat ss
                                            then GCA.Tfloat_Complex noOrigin
                                            else if any isLong ss
                                                then GCA.Tlong_double_Complex noOrigin
                                                else GCA.Tdouble_Complex noOrigin
transTypeSpecs ss | (any isDouble ss)  = if any isLong ss 
                                            then GCA.Tlong_double noOrigin
                                            else GCA.Tdouble noOrigin
transTypeSpecs ss | (any isLong ss)    = if hasLongLong ss 
                                            then GCA.Tlong_long (sign ss) noOrigin
                                            else GCA.Tlong (sign ss) noOrigin
transTypeSpecs ss | (any isInt ss)     = GCA.Tint (sign ss) noOrigin
transTypeSpecs ss | (any isSigned ss)  = GCA.Tint (sign ss) noOrigin
transTypeSpecs ss | (any isUnsigned ss)= GCA.Tint (sign ss) noOrigin
transTypeSpecs ss | (any isFloat ss)   = GCA.Tfloat noOrigin
transTypeSpecs ss | (any isFloatN ss)  = 
    error $ "Gencot unsupported C: CFloatNType at " ++ (show $ LCN.nodeInfo $ head ss)
transTypeSpecs ss | (any isBool ss)    = GCA.T_Bool noOrigin
transTypeSpecs ss | (any isInt128 ss)  = 
    error $ "Gencot unsupported C: CInt128Type at " ++ (show $ LCN.nodeInfo $ head ss)
transTypeSpecs ((LC.CSUType su n):_)  = transStructUnion su
transTypeSpecs ((LC.CEnumType enum@(LC.CEnum mid _ _ _) n):_) = 
    GCA.Tenum (fmap (transIdent noOrigin) mid) (transEnum enum) [] noOrigin
transTypeSpecs ((LC.CTypeDef ident n):_) = GCA.Tnamed (transIdent noOrigin ident) [] noOrigin
transTypeSpecs ((LC.CTypeOfExpr expr n):_) = GCA.TtypeofExp (transExpr noOrigin expr) noOrigin
transTypeSpecs ((LC.CTypeOfType decl n):_) = GCA.TtypeofType (declToType decl) noOrigin
transTypeSpecs ss | (any isAtomic ss)  = 
    error $ "Gencot unsupported C: CAtomicType at " ++ (show $ LCN.nodeInfo $ head ss)

sign ss = if any isSigned ss then (Just $ Tsigned noOrigin)
                             else if any isUnsigned ss then (Just $ Tunsigned noOrigin)
                                                       else Nothing
isVoid (LC.CVoidType _) = True
isVoid _ = False
isChar (LC.CCharType _) = True
isChar _ = False
isShort (LC.CShortType _) = True
isShort _ = False
isInt (LC.CIntType _) = True
isInt _ = False
isLong (LC.CLongType _) = True
isLong _ = False
isFloat (LC.CFloatType _) = True
isFloat _ = False
isFloatN (LC.CFloatNType _ _ _) = True
isFloatN _ = False
isDouble (LC.CDoubleType _) = True
isDouble _ = False
isSigned (LC.CSignedType _) = True
isSigned _ = False
isUnsigned (LC.CUnsigType _) = True
isUnsigned _ = False
isBool (LC.CBoolType _) = True
isBool _ = False
isComplex (LC.CComplexType _) = True
isComplex _ = False
isInt128 (LC.CInt128Type _) = True
isInt128 _ = False
isAtomic (LC.CAtomicType _ _) = True
isAtomic _ = False
hasLongLong ss = (length (filter isLong ss)) > 1

declToType :: LC.CDecl -> GCA.Type
declToType (LC.CDecl specs [((Just dclr@(LC.CDeclr _ _ _ cattrs ndeclr)),_,_)] ndecl) =
    checkDeclr "typename" dclr
       GCA.Type (transDeclSpecs specs) (transDeclr dclr) noOrigin
declToType (LC.CDecl specs [] n) =
    GCA.Type (transDeclSpecs specs) (GCA.DeclRoot noOrigin) noOrigin

transTypeQual :: LC.CTypeQual -> GCA.TypeQual
transTypeQual (LC.CConstQual n) = GCA.Tconst noOrigin
transTypeQual (LC.CVolatQual n) = GCA.Tvolatile noOrigin
transTypeQual (LC.CRestrQual n) = GCA.Trestrict noOrigin
transTypeQual (LC.CAtomicQual n) = 
    error $ "Gencot unsupported C: CAtomicQual at " ++ show n
transTypeQual (LC.CAttrQual a)  = GCA.TAttr $ transAttr a
transTypeQual (LC.CNullableQual n) =
    error $ "Gencot unsupported C: CNullableQual at " ++ show n
transTypeQual (LC.CNonnullQual n) =
    error $ "Gencot unsupported C: CNonnullQual at " ++ show n

transFunSpec :: LC.CFunSpec -> GCA.TypeQual
transFunSpec (LC.CInlineQual n) = GCA.Tinline noOrigin
transFunSpec (LC.CNoreturnQual n) = 
    error $ "Gencot unsupported C: CNoreturnQual at " ++ show n

transStructUnion :: LC.CStructUnion -> GCA.TypeSpec
transStructUnion (LC.CStruct CStructTag mid mcds cattrs n) =
    GCA.Tstruct (fmap (transIdent noOrigin) mid) (fmap (map transMemberDecl) mcds) (map transAttr cattrs) noOrigin
transStructUnion (LC.CStruct CUnionTag mid mcds cattrs n) =
    GCA.Tunion (fmap (transIdent noOrigin) mid) (fmap (map transMemberDecl) mcds) (map transAttr cattrs) noOrigin

transEnum :: LC.CEnum -> [GCA.CEnum]
transEnum (LC.CEnum _ Nothing _ n) = []
transEnum (LC.CEnum _ (Just vals) _ n) = map transEnumerator vals
    where transEnumerator (name, mexpr) = GCA.CEnum (transIdent noOrigin name) (fmap (transExpr noOrigin) mexpr) noOrigin

transDeclr :: LC.CDeclr -> GCA.Decl
transDeclr dclr@(LC.CDeclr _ derived_declrs _ _ n) = transDerivedDeclrs derived_declrs

transDerivedDeclrs :: [LC.CDerivedDeclr] -> GCA.Decl
transDerivedDeclrs ds = foldr accdclr (GCA.DeclRoot noOrigin) ds
    where 
        accdclr :: LC.CDerivedDeclr -> GCA.Decl -> GCA.Decl
        accdclr (LC.CPtrDeclr quals _) dcl =
            GCA.Ptr (map transTypeQual quals) dcl noOrigin
        accdclr (LC.CArrDeclr quals size _) dcl =
            GCA.Array (map transTypeQual quals) (transArrSize size) dcl noOrigin
        accdclr fd@(LC.CFunDeclr _ _ _ ) dcl =
            GCA.Proto dcl (transParams fd) noOrigin

transParams :: LC.CDerivedDeclr -> GCA.Params
transParams (LC.CFunDeclr (Right (decls, isVariadic)) _{-fun_attrs-} n) = 
    GCA.Params (map transParamDecl decls) isVariadic noOrigin

transArrSize :: LC.CArrSize -> GCA.ArraySize
transArrSize (LC.CNoArrSize True) = GCA.VariableArraySize noOrigin
transArrSize (LC.CNoArrSize False) = GCA.NoArraySize noOrigin
transArrSize (LC.CArrSize staticMod expr) = GCA.ArraySize staticMod (transExpr noOrigin expr) noOrigin

transInit :: LC.CInit -> GCA.Initializer
transInit (LC.CInitExpr expr n) = GCA.ExpInitializer (transExpr noOrigin expr) noOrigin
transInit (LC.CInitList initl n) = GCA.CompoundInitializer (map transDesig initl) noOrigin

transDesig :: ([LC.CDesignator], LC.CInit) -> (Maybe GCA.Designation, GCA.Initializer)
transDesig ([],ini) = (Nothing,transInit ini)
transDesig (desigs,ini) = (Just (GCA.Designation (map transDesignator desigs) noOrigin),transInit ini)

transDesignator :: LC.CDesignator -> GCA.Designator
transDesignator (LC.CArrDesig expr n) = GCA.IndexDesignator (transExpr noOrigin expr) noOrigin
transDesignator (LC.CMemberDesig ident n) = GCA.MemberDesignator (transIdent noOrigin ident) noOrigin
transDesignator (LC.CRangeDesig expr1 expr2 n) =
    error $ "Gencot unsupported C: CRangeDesig at " ++ show n

transAttr :: LC.CAttr -> GCA.Attr
transAttr (LC.CAttr attrName attrParams n) = GCA.Attr (transIdent noOrigin attrName) (map (transExpr noOrigin) attrParams) noOrigin

transExpr :: Origin -> LC.CExpr -> GCA.Exp
transExpr o (LC.CComma [] n) = 
    error $ "Gencot unsupported C: CComma [] at " ++ show n
transExpr o (LC.CComma (_:[]) n) =
    error $ "Gencot unsupported C: CComma [expr] at " ++ show n
transExpr o (LC.CComma exprs n) = 
    if (length exprs) == 2
       then GCA.Seq (transExpr noOrigin $ head exprs) (transExpr noOrigin $ head $ tail exprs) o
       else GCA.Seq (transExpr noOrigin $ head exprs) (transExpr noOrigin $ (LC.CComma (tail exprs) n)) o
transExpr o (LC.CAssign op expr1 expr2 n) = GCA.Assign (transExpr noOrigin expr1) (transAssignOp op) (transExpr noOrigin expr2) o
transExpr o (LC.CCond expr1 Nothing expr3 n) = 
    error $ "Gencot unsupported C: CCond expr Nothing expr at " ++ show n
transExpr o (LC.CCond expr1 (Just expr2) expr3 n) = 
    GCA.Cond (transExpr noOrigin expr1) (transExpr noOrigin expr2) (transExpr noOrigin expr3) o
transExpr o (LC.CBinary op expr1 expr2 n) = GCA.BinOp (transBinaryOp op) (transExpr noOrigin expr1) (transExpr noOrigin expr2) o
transExpr o (LC.CCast decl expr n) = GCA.Cast (declToType decl) (transExpr noOrigin expr) o
transExpr o (LC.CUnary LC.CPreIncOp expr n) = GCA.PreInc (transExpr noOrigin expr) o
transExpr o (LC.CUnary LC.CPreDecOp expr n) = GCA.PreDec (transExpr noOrigin expr) o
transExpr o (LC.CUnary LC.CPostIncOp expr n) = GCA.PostInc (transExpr noOrigin expr) o
transExpr o (LC.CUnary LC.CPostDecOp expr n) = GCA.PostDec (transExpr noOrigin expr) o
transExpr o (LC.CUnary op expr n) = GCA.UnOp (transUnaryOp op) (transExpr noOrigin expr) o
transExpr o (LC.CSizeofExpr expr n) = GCA.SizeofExp (transExpr noOrigin expr) o
transExpr o (LC.CSizeofType decl n) = GCA.SizeofType (declToType decl) o
transExpr o (LC.CAlignofExpr expr n) =
    error $ "Gencot unsupported C: CAlignofExpr at " ++ show n
transExpr o (LC.CAlignofType decl n) =
    error $ "Gencot unsupported C: CAlignofType at " ++ show n
transExpr o (LC.CComplexReal expr n) =
    error $ "Gencot unsupported C: CComplexReal at " ++ show n
transExpr o (LC.CComplexImag expr n) =
    error $ "Gencot unsupported C: CComplexImag at " ++ show n
transExpr o (LC.CIndex expr1 expr2 n) = GCA.Index (transExpr noOrigin expr1) (transExpr noOrigin expr2) o
transExpr o (LC.CCall expr args n) = GCA.FnCall (transExpr noOrigin expr) (map (transExpr noOrigin) args) o
transExpr o (LC.CMember expr ident True n) = GCA.PtrMember (transExpr noOrigin expr) (transIdent noOrigin ident) o
transExpr o (LC.CMember expr ident False n) = GCA.Member (transExpr noOrigin expr) (transIdent noOrigin ident) o
transExpr o (LC.CVar ident n) = GCA.Var (transIdent noOrigin ident) o
transExpr o (LC.CConst constant) = GCA.Const (transConst constant) o
transExpr o (LC.CCompoundLit decl initl n) = GCA.CompoundLit (declToType decl) (map transDesig initl) o
transExpr o (LC.CStatExpr (LC.CCompound _{-localLabels-} bis nstat) nexpr) = 
    GCA.StmExpr (zipWith transBlockItem (subListOrigins nexpr bis) bis) o -- is GCA.StmExpr correct here?
transExpr o (LC.CStatExpr stat n) = GCA.StmExpr [GCA.BlockStm (transStat noOrigin stat)] o
transExpr o (LC.CLabAddrExpr ident n) = 
    error $ "Gencot unsupported C: CLabAddrExpr at " ++ show n
transExpr o (LC.CGenericSelection expr assoc_list n) =
    error $ "Gencot unsupported C: CGenericSelection at " ++ show n
transExpr o (LC.CBuiltinExpr builtin) = transBuiltin builtin

transBuiltin :: LC.CBuiltin -> GCA.Exp
transBuiltin (LC.CBuiltinVaArg expr ty_name n) = GCA.BuiltinVaArg (transExpr noOrigin expr) (declToType ty_name) noOrigin
transBuiltin (LC.CBuiltinOffsetOf _ty_name otherDesigs n) =
    error $ "Gencot unsupported C: CBuiltinOffsetOf at " ++ show n
transBuiltin (LC.CBuiltinTypesCompatible ty1 ty2 n) =
    error $ "Gencot unsupported C: CBuiltinTypesCompatible at " ++ show n
transBuiltin (LC.CBuiltinConvertVector expr ty n)  =
    error $ "Gencot unsupported C: CBuiltinConvertVector at " ++ show n

transSubExpr :: LCN.NodeInfo -> LC.CExpr -> GCA.Exp
transSubExpr n expr = transExpr (subOrigin n expr) expr

transAssignOp :: LC.CAssignOp -> GCA.AssignOp
transAssignOp op = case op of
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

transBinaryOp :: LC.CBinaryOp -> GCA.BinOp
transBinaryOp op = case op of
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

transUnaryOp :: LC.CUnaryOp -> GCA.UnOp
transUnaryOp op = case op of
    LC.CAdrOp     -> GCA.AddrOf
    LC.CIndOp     -> GCA.Deref
    LC.CPlusOp    -> GCA.Positive
    LC.CMinOp     -> GCA.Negate
    LC.CCompOp    -> GCA.Not
    LC.CNegOp     -> GCA.Lnot

transConst :: LC.CConst -> GCA.Const
transConst (LC.CIntConst   (LC.CInteger i rep flags) n) =
    if LC.testFlag LC.FlagLongLong flags
       then GCA.LongLongIntConst (raw rep i) (signed flags) i noOrigin
       else if LC.testFlag LC.FlagLong flags
            then GCA.LongIntConst (raw rep i) (signed flags) i noOrigin
            else GCA.IntConst (raw rep i) (signed flags) i noOrigin
transConst (LC.CCharConst  (LC.CChar chr wd) n) = 
    GCA.CharConst (prewd wd $ LC.showCharConst chr "") chr noOrigin
{- Multicharacter char constants cannot be fully represented in language-c-quote,
   since GCA.CharConst uses a single Haskell char. 
   We generate only the raw representation and set the actual representation to ' '. 
   This is sufficient for prettyprinting. -}
transConst (LC.CCharConst  (LC.CChars chrs wd) n) = 
    GCA.CharConst (prewd wd ("'"++(init $ tail $ LC.showStringLit chrs "")++"'")) ' ' noOrigin
{- Float constants are only represented in their raw form in language-c.
   Therefore we only transfer the raw representation to language-c-quote and set the actual float to 1.0.
   This is sufficient for prettyprinting, since language-c always generates positive float constants
   and language-c-quote uses only the sign of the actual representation for operator precedence. -}
transConst (LC.CFloatConst (LC.CFloat str) n) = 
    GCA.FloatConst str 1.0 noOrigin
{- Sequences of String literals are concatenated by language-c.
   Therefore we cannot transfer the original sequence to language-c-quote.
   The prettyprinter directly uses the raw representation, therefore we only generate that. -}
transConst (LC.CStrConst   (LC.CString str wd) n) = 
    GCA.StringConst [prewd wd $ LC.showStringLit str ""] "" noOrigin

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

transStrLit :: LC.CStrLit -> GCA.StringLit
transStrLit (LC.CStrLit (LC.CString str wd) n) = GCA.StringLit [prewd wd $ LC.showStringLit str ""] "" noOrigin

transIdent :: Origin -> LCI.Ident -> GCA.Id
transIdent o (LCI.Ident name _ n) = GCA.Id name o

transSubIdent :: LCN.NodeInfo -> LC.Ident -> GCA.Id
transSubIdent n ident = transIdent (subOrigin n ident) ident
