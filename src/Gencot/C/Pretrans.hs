{-# LANGUAGE PackageImports #-}
module Gencot.C.Pretrans where

import Language.C.Syntax.AST
import Language.C.Syntax.Constants (cInteger)
import Language.C.Data.Node (undefNode)

pretransStat :: CStat -> CStat
pretransStat (CLabel nam s as n) = (CLabel nam (pretransStat s) as n)  -- expressions in attribute list as are not transformed
pretransStat (CCase e s n) = (CCase (pretransExpr e) (pretransStat s) n)
pretransStat (CCases e1 e2 s n) = (CCases (pretransExpr e1) (pretransExpr e2) (pretransStat s) n)
pretransStat (CDefault s n) = (CDefault (pretransStat s) n)
pretransStat (CExpr me n) = (CExpr (fmap pretransExpr me) n)
pretransStat (CCompound nams bis n) = (CCompound nams (fmap pretransBlockItem bis) n)
pretransStat (CIf e s1 ms2 n) = (CIf (pretransExpr e) (pretransStat s1) (fmap pretransStat ms2) n)
pretransStat (CSwitch e s n) = (CSwitch (pretransExpr e) (pretransStat s) n)
pretransStat (CWhile e s dow n) = (CWhile (pretransExpr e) (pretransStat s) dow n)
pretransStat (CFor (Left me) me2 me3 s n) = (CFor (Left (fmap pretransExpr me)) (fmap pretransExpr me2) (fmap pretransExpr me3) (pretransStat s) n)
pretransStat (CFor (Right d) me2 me3 s n) = (CFor (Right (pretransDecl d)) (fmap pretransExpr me2) (fmap pretransExpr me3) (pretransStat s) n)
pretransStat (CGotoPtr e n) = (CGotoPtr (pretransExpr e) n)
pretransStat (CReturn me n) = (CReturn (fmap pretransExpr me) n)
pretransStat s = s
-- Expressions in asm statements are not transformed.

pretransExpr :: CExpr -> CExpr
pretransExpr (CUnary CPreIncOp e n) = pretransExpr (CAssign CAddAssOp e (CConst $ CIntConst (cInteger 1) undefNode) n)
pretransExpr (CUnary CPreDecOp e n) = pretransExpr (CAssign CSubAssOp e (CConst $ CIntConst (cInteger 1) undefNode) n)
pretransExpr (CAssign CMulAssOp e1 e2 n) = pretransExpr (CAssign CAssignOp e1 (CBinary CMulOp e1 e2 undefNode) n)
pretransExpr (CAssign CDivAssOp e1 e2 n) = pretransExpr (CAssign CAssignOp e1 (CBinary CDivOp e1 e2 undefNode) n)
pretransExpr (CAssign CRmdAssOp e1 e2 n) = pretransExpr (CAssign CAssignOp e1 (CBinary CRmdOp e1 e2 undefNode) n)
pretransExpr (CAssign CAddAssOp e1 e2 n) = pretransExpr (CAssign CAssignOp e1 (CBinary CAddOp e1 e2 undefNode) n)
pretransExpr (CAssign CSubAssOp e1 e2 n) = pretransExpr (CAssign CAssignOp e1 (CBinary CSubOp e1 e2 undefNode) n)
pretransExpr (CAssign CShlAssOp e1 e2 n) = pretransExpr (CAssign CAssignOp e1 (CBinary CShlOp e1 e2 undefNode) n)
pretransExpr (CAssign CShrAssOp e1 e2 n) = pretransExpr (CAssign CAssignOp e1 (CBinary CShrOp e1 e2 undefNode) n)
pretransExpr (CAssign CAndAssOp e1 e2 n) = pretransExpr (CAssign CAssignOp e1 (CBinary CAndOp e1 e2 undefNode) n)
pretransExpr (CAssign CXorAssOp e1 e2 n) = pretransExpr (CAssign CAssignOp e1 (CBinary CXorOp e1 e2 undefNode) n)
pretransExpr (CAssign COrAssOp  e1 e2 n) = pretransExpr (CAssign CAssignOp e1 (CBinary COrOp  e1 e2 undefNode) n)

pretransExpr (CComma es n) = (CComma (fmap pretransExpr es) n)
pretransExpr (CAssign op e1 e2 n) = (CAssign op (pretransExpr e1) (pretransExpr e2) n)
pretransExpr (CCond e1 me2 e3 n) = (CCond (pretransExpr e1) (fmap pretransExpr me2) (pretransExpr e3) n)
pretransExpr (CBinary op e1 e2 n) = (CBinary op (pretransExpr e1) (pretransExpr e2) n)
pretransExpr (CCast d e n) = (CCast (pretransDecl d) (pretransExpr e) n)
pretransExpr (CUnary op e n) = (CUnary op (pretransExpr e) n)
pretransExpr (CSizeofExpr e n) = (CSizeofExpr (pretransExpr e) n)
pretransExpr (CSizeofType d n) = (CSizeofType (pretransDecl d) n)
pretransExpr (CAlignofExpr e n) = (CAlignofExpr (pretransExpr e) n)
pretransExpr (CAlignofType d n) = (CAlignofType (pretransDecl d) n)
pretransExpr (CComplexReal e n) = (CComplexReal (pretransExpr e) n)
pretransExpr (CComplexImag e n) = (CComplexImag (pretransExpr e) n)
pretransExpr (CIndex e1 e2 n) = (CIndex (pretransExpr e1) (pretransExpr e2) n)
pretransExpr (CCall e es n) = (CCall (pretransExpr e) (fmap pretransExpr es) n)
pretransExpr (CMember e nam arrow n) = (CMember (pretransExpr e) nam arrow n)
pretransExpr (CStatExpr s n) = (CStatExpr (pretransStat s) n)
pretransExpr e = e
-- compound literals, generic selections, and builtin expressions are not transformed.

pretransBlockItem :: CBlockItem -> CBlockItem
pretransBlockItem (CBlockStmt s) = (CBlockStmt (pretransStat s))
pretransBlockItem (CBlockDecl d) = (CBlockDecl (pretransDecl d))
pretransBlockItem bi = bi
-- expressions in nested function definitions are not transformed

pretransDecl :: CDecl -> CDecl
pretransDecl (CDecl ss ds n) = (CDecl ss (map (\(md,mi,me)->(md,fmap pretransInit mi,me)) ds) n)-- only expressions in initialzers are transformed
pretransDecl d = d
-- expressions in static asserts are not transformed

pretransInit :: CInit -> CInit
pretransInit (CInitExpr e n) = (CInitExpr (pretransExpr e) n)
pretransInit (CInitList l n) = (CInitList (map (\(ds,i)->(map pretransDesig ds,pretransInit i)) l) n)

pretransDesig :: CDesignator -> CDesignator
pretransDesig (CArrDesig e n) = (CArrDesig (pretransExpr e) n)
pretransDesig (CRangeDesig e1 e2 n) = (CRangeDesig (pretransExpr e1) (pretransExpr e2) n)
pretransDesig d = d
