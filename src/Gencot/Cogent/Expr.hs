{-# LANGUAGE PackageImports #-}
module Gencot.Cogent.Expr where

import Cogent.Surface as CS
import Cogent.Common.Syntax as CCS

import Gencot.Origin (noOrigin)
import Gencot.Cogent.Ast -- includes unitType
import Gencot.Cogent.Types (
  mkU8Type, mkU32Type, mkStringType, mkBoolType,
  mkTupleType, mkCtlType, mkFunType, mkRecordType, mkTakeType, mkArrTakeType, getResultType)

-- Variable name together with its type
type TypedVar = (CCS.VarName,GenType)

-- Function name together with its type
type TypedFun = (CCS.FunName,GenType)

-- Construct Expressions
------------------------

genExpr t e = GenExpr e noOrigin t Nothing

-- construct ()
mkUnitExpr :: GenExpr
mkUnitExpr = genExpr unitType CS.Unitel

-- construct i
mkIntLitExpr :: GenType -> Integer -> GenExpr
mkIntLitExpr t = (genExpr t) . CS.IntLit

-- construct c
-- in C a character constant has type int!
mkCharLitExpr :: Char -> GenExpr
mkCharLitExpr = (genExpr mkU32Type) . CS.CharLit

-- construct s
mkStringLitExpr :: String -> GenExpr
mkStringLitExpr = (genExpr mkStringType) . CS.StringLit

-- construct True or False
mkBoolLitExpr :: Bool -> GenExpr
mkBoolLitExpr = (genExpr mkBoolType) . CS.BoolLit

-- construct v
mkVarExpr :: TypedVar -> GenExpr
mkVarExpr (v,t) = genExpr t $ CS.Var v

-- construct i as control value
mkCtlLitExpr :: Integer -> GenExpr
mkCtlLitExpr i = mkIntLitExpr mkCtlType i

-- construct (e1,..,en) or e1
mkTupleExpr :: [GenExpr] -> GenExpr
mkTupleExpr [e] = e
mkTupleExpr es = genExpr (mkTupleType (map typOfGE es)) $ CS.Tuple es

-- construct e1 op e2 or op e1
mkOpExpr :: GenType -> CCS.OpName -> [GenExpr] -> GenExpr
mkOpExpr t op es = genExpr t $ CS.PrimOp op es

-- construct e1 op e2 or op e1 for op with boolean result
mkBoolOpExpr :: CCS.OpName -> [GenExpr] -> GenExpr
mkBoolOpExpr = mkOpExpr mkBoolType

-- construct (<control value>,v1,...,vn) or <control value>
mkCtlVarTupleExpr :: Integer -> [TypedVar] -> GenExpr
mkCtlVarTupleExpr cv vs = mkExpVarTupleExpr (mkCtlLitExpr cv) vs

-- construct (v1,...,vn) or v1
mkVarTupleExpr :: [CCS.VarName] -> GenExpr
mkVarTupleExpr vs = mkTupleExpr $ map mkVarExpr vs

-- construct (e,v1,...,vn) or e
mkExpVarTupleExpr :: GenExpr -> [TypedVar] -> GenExpr
mkExpVarTupleExpr e [] = e
mkExpVarTupleExpr e vs = mkTupleExpr (e : (map mkVarExpr vs))

-- construct (0,v1,...,vn) or 0
mk0VarTupleExpr :: [TypedVar] -> GenExpr
mk0VarTupleExpr vs = mkExpVarTupleExpr (mkCtlLitExpr 0) vs

-- construct e1 || ... || en
mkDisjExpr :: [GenExpr] -> GenExpr
mkDisjExpr [] = mkBoolLitExpr False
mkDisjExpr [e] = e
mkDisjExpr (e : es) = mkBoolOpExpr "||" [e,mkDisjExpr es]

-- replace e1 in (e1,...,en) or e1
replaceLeadExpr :: GenExpr -> GenExpr -> GenExpr
replaceLeadExpr e (GenExpr (CS.Tuple es) o (CS.TTuple ts) src) = 
    GenExpr (CS.Tuple (e : tail es)) o (CS.TTuple ((typOfGE e) : tail ts)) src
replaceLeadExpr e _ = e

-- construct f () or f e1 or f (e1,..,en)
mkAppExpr :: TypedFun -> [GenExpr] -> GenExpr
mkAppExpr (f,t) es = genExpr (getResultType t) $ CS.App (genExpr t $ CS.Var f) (arg es) False
    where arg [] = mkUnitExpr
          arg [e] = e
          arg es = mkTupleExpr es

-- construct f[t1..] () or f[t1..] e1 or f[t1..] (e1,..,en)
mkTypedAppExpr :: TypedFun -> [Maybe GenType] -> [GenExpr] -> GenExpr
mkTypedAppExpr (f,t) ts es = genExpr (getResultType t) $ CS.App (genExpr t $ CS.TLApp f ts [] NoInline) (arg es) False
    where arg [] = mkUnitExpr
          arg [e] = e
          arg es = mkTupleExpr es

-- construct let b1 and ... and bn in e
mkLetExpr :: [GenBnd] -> GenExpr -> GenExpr
mkLetExpr bs e =
    genExpr (typOfGE e) $ CS.Let bs e

-- construct v1{f=v2}
mkRecPutExpr :: TypedVar -> TypedVar -> CCS.FieldName -> GenExpr
mkRecPutExpr tv1@(v1,t1) tv2 f = genExpr (mkTakeType False t1 [f]) $ CS.Put (mkVarExpr tv1) [Just (f,mkVarExpr tv2)]

-- construct v1 @{@v3=v2}
mkArrPutExpr :: TypedVar -> TypedVar -> TypedVar -> GenExpr
mkArrPutExpr tv1@(v1,t1) tv2 tv3 = genExpr (mkArrTakeType False t1 [e3]) $ CS.ArrayPut (mkVarExpr tv1) [(e3,mkVarExpr tv2)]
    where e3 = mkVarExpr tv3

-- construct if e0 then e1 else e2
mkIfExpr :: GenExpr -> GenExpr -> GenExpr -> GenExpr
mkIfExpr e0 e1 e2 = genExpr (typOfGE e1) $ CS.If e0 [] e1 e2

-- construct e | C1 v11 .. v1n1 -> e1 | ... | Ck vk1 .. vknk -> ek
mkMatchExpr :: GenExpr -> [(CCS.TagName,[TypedVar],GenExpr)] -> GenExpr
mkMatchExpr e as = genExpr (getTyp $ head as) $ CS.Match e [] $ map mkAlt as
    where mkAlt (tag,vars,ae) = CS.Alt (GenPatn (CS.PCon tag $ map mkVarPattern vars) (typOfGE e) noOrigin) CCS.Regular ae
          getTyp (_,_,ae) = typOfGE ae

-- construct #{f1 = e1, ... ,fn = en}
mkRecordExpr :: [(CCS.FieldName,GenExpr)] -> GenExpr
mkRecordExpr flds = genExpr (mkRecordType (map (\(f,e) -> (f,typOfGE e)) flds) $ CS.UnboxedRecord flds

-- construct \p => e
mkLambdaExpr :: GenIrrefPatn -> GenExpr -> GenExpr
mkLambdaExpr p e = genExpr (mkFunType (typOfGIP p) (typOfGE e)) $ CS.Lam p Nothing e

-- construct let (_,...) = expr in e
mkBodyExpr :: GenBnd -> GenExpr -> GenExpr
mkBodyExpr b@(CS.Binding ip _ _ _) e = mkLetExpr [replaceLeadPatn mkWildcardPattern (typOfGIP ip) b] e

-- construct let ... in v<n>'
mkPlainExpr :: BindsPair -> GenExpr
mkPlainExpr (main,putback) = 
    if not $ null putback
       then toDummyExpr e $ mkDummyExpr "No putback obligations supported in plain expression."
       else 
       if (length vs) > 1
          then toDummyExpr e $ mkDummyExpr "No side effects supported in plain expression."
          else mkLetExpr (reverse main) $ mkVarExpr $ head vs
    where (CS.Binding ip _ e _) = head main
          vs = tupleVars ip

-- construct (gencotDummy msg)
mkDummyExpr :: String -> GenExpr
mkDummyExpr msg = mkAppExpr unitType "gencotDummy" [mkStringLitExpr msg]

-- turn expression to dummy, preserving origin, type, and source
toDummyExpr :: GenExpr -> GenExpr -> GenExpr
toDummyExpr (GenExpr e o t src) (GenExpr dummy _ _ _) = (GenExpr dummy o t src) 
