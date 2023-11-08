{-# LANGUAGE PackageImports #-}
module Gencot.Cogent.Expr where

import Data.List (union,nub,(\\))
import Data.Maybe (catMaybes)

import Cogent.Surface as CS
import Cogent.Common.Syntax as CCS

import Gencot.Origin (Origin,noOrigin)
import Gencot.Names (mapNull)
import Gencot.Cogent.Ast -- includes unitType, CSrc
import Gencot.Cogent.Types (
  mkU8Type, mkU32Type, mkStringType, mkBoolType,
  mkTupleType, mkCtlType, mkFunType, mkRecordType, mkVoidPtrType, mkTakeType, mkArrTakeType, mkMayNull,
  getResultType)

-- Variable name together with its type
data TypedVar = TV {
    namOfTV :: CCS.VarName,
    typOfTV :: GenType
} deriving (Show)
-- Equality by name only
instance Eq TypedVar where
    v1 == v2 = (namOfTV v1) == (namOfTV v2)

-- Function name together with its type
type TypedFun = (CCS.FunName,GenType)

funResultType :: TypedFun -> GenType
funResultType (_, t) = getResultType t

-- Construct Expressions
------------------------

genExpr t e = GenExpr e noOrigin t Nothing

genExpr' o t c e = GenExpr e o t c

-- construct ()
mkUnitExpr :: GenExpr
mkUnitExpr = genExpr unitType CS.Unitel

-- construct i
mkIntLitExpr :: GenType -> Integer -> GenExpr
mkIntLitExpr t = (genExpr t) . CS.IntLit

-- construct c
-- in C a character constant has type int!
mkCharLitExpr :: Char -> GenExpr
mkCharLitExpr = (genExpr mkU8Type) . CS.CharLit

-- construct s
mkStringLitExpr :: String -> GenExpr
mkStringLitExpr = (genExpr mkStringType) . CS.StringLit

-- construct True or False
mkBoolLitExpr :: Bool -> GenExpr
mkBoolLitExpr = (genExpr mkBoolType) . CS.BoolLit

-- construct cogent_NULL
mkNullExpr :: GenExpr
mkNullExpr = mkVarExpr $ TV mapNull $ mkMayNull mkVoidPtrType

-- construct v
mkVarExpr :: TypedVar -> GenExpr
mkVarExpr (TV v t) = genExpr t $ CS.Var v

-- construct f
mkFunExpr :: TypedFun -> GenExpr
mkFunExpr (f,t) = genExpr t $ CS.Var f

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

-- construct upcast e
mkUpcastExpr :: GenType -> GenExpr -> GenExpr
mkUpcastExpr t e = genExpr t $ CS.Upcast e

-- construct (<control value>,v1,...,vn) or <control value>
mkCtlVarTupleExpr :: Integer -> [TypedVar] -> GenExpr
mkCtlVarTupleExpr cv vs = mkExpVarTupleExpr (mkCtlLitExpr cv) vs

-- construct (v1,...,vn) or v1
mkVarTupleExpr :: [TypedVar] -> GenExpr
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
replaceLeadExpr e (GenExpr (CS.Tuple es) o (GenType (CS.TTuple ts) ot _) src) =
    GenExpr (CS.Tuple (e : tail es)) o (GenType (CS.TTuple ((typOfGE e) : tail ts)) ot Nothing) src
replaceLeadExpr e _ = e

-- construct f(e)
mkAppExpr :: GenExpr -> GenExpr -> GenExpr
mkAppExpr f e = genExpr (getResultType $ typOfGE f) $ CS.App f e False

-- construct f[t1..]
mkTopLevelFunExpr :: TypedFun -> [Maybe GenType] -> GenExpr
mkTopLevelFunExpr (f,t) ts = genExpr t $ CS.TLApp f ts [] NoInline

-- construct let b1 and ... and bn in e
mkLetExpr :: [GenBnd] -> GenExpr -> GenExpr
mkLetExpr bs e =
    genExpr (typOfGE e) $ CS.Let bs e

-- construct v1{f=v2}
mkRecPutExpr :: TypedVar -> TypedVar -> CCS.FieldName -> GenExpr
mkRecPutExpr tv1@(TV v1 t1) tv2 f = genExpr t1 $ CS.Put (mkVarExpr tv1) [Just (f,mkVarExpr tv2)]

-- construct v1 @{@v3=v2}
mkArrPutExpr :: TypedVar -> TypedVar -> TypedVar -> GenExpr
mkArrPutExpr tv1@(TV v1 t1) tv2 tv3 = genExpr t1 $ CS.ArrayPut (mkVarExpr tv1) [(e3,mkVarExpr tv2)]
    where e3 = mkVarExpr tv3

-- construct if e0 then e1 else e2
-- The first argument is the type of the resulting expression.
mkIfExpr :: GenType -> GenExpr -> GenExpr -> GenExpr -> GenExpr
mkIfExpr t e0 e1 e2 = genExpr t $ CS.If e0 [] e1 e2

-- construct e | C1 v11 .. v1n1 -> e1 | ... | Ck vk1 .. vknk -> ek
mkMatchExpr :: Origin -> GenType -> CSrc -> GenExpr -> [(CCS.TagName,[GenIrrefPatn],GenExpr)] -> GenExpr
mkMatchExpr o t c e as = genExpr' o t c $ CS.Match e [] $ map mkAlt as
    where mkAlt (tag,varpats,ae) = CS.Alt (GenPatn (CS.PCon tag varpats) noOrigin (typOfGE e)) CCS.Regular ae

-- construct #{f1 = e1, ... ,fn = en}
mkRecordExpr :: [(CCS.FieldName,GenExpr)] -> GenExpr
mkRecordExpr flds = genExpr (mkRecordType (map (\(f,e) -> (f,typOfGE e)) flds)) $ CS.UnboxedRecord flds

-- construct \p => e
mkLambdaExpr :: GenIrrefPatn -> GenExpr -> GenExpr
mkLambdaExpr p e = genExpr (mkFunType (typOfGIP p) (typOfGE e)) $ CS.Lam p Nothing e

-- construct e.f
mkMemberExpr :: GenType -> GenExpr -> CCS.FieldName -> GenExpr
mkMemberExpr t e f = genExpr t $ CS.Member e f

isPutExprFor :: CCS.VarName -> GenExpr -> Bool
isPutExprFor v (GenExpr (CS.Put _ [Just (_, GenExpr (CS.Var ev) _ _ _)]) _ _ _) = v == ev
isPutExprFor v (GenExpr (CS.ArrayPut _ [(_, GenExpr (CS.Var ev) _ _ _)]) _ _ _) = v == ev
isPutExprFor _ _ = False

-- Determine free typed variables in expressions
------------------------------------------------

-- | Retrieve the free variables with their types.
-- Toplevel defined functions (used in TLApp expressions) are omitted.
getFreeTypedVars :: GenExpr -> [TypedVar]
getFreeTypedVars (GenExpr (CS.Var nam) _ t _) = [(TV nam t)]
getFreeTypedVars (GenExpr (CS.PrimOp _ es) _ _ _) = nub $ concat $ map getFreeTypedVars es
getFreeTypedVars (GenExpr (CS.Match e _ alts) _ _ _) = union (getFreeTypedVars e) $ nub $ concat $ map getFreeTypedVarsInAlt alts
getFreeTypedVars (GenExpr (CS.TLApp _ _ _ _) _ _ _) = []
getFreeTypedVars (GenExpr (CS.Con _ es) _ _ _) = nub $ concat $ map getFreeTypedVars es
getFreeTypedVars (GenExpr (CS.Seq e1 e2) _ _ _) = union (getFreeTypedVars e1) (getFreeTypedVars e2)
getFreeTypedVars (GenExpr (CS.Lam ip _ e) _ _ _) = (getFreeTypedVars e) \\ (getBoundTypedVars ip)
getFreeTypedVars (GenExpr (CS.App e1 e2 _) _ _ _) = union (getFreeTypedVars e1) (getFreeTypedVars e2)
getFreeTypedVars (GenExpr (CS.Comp e1 e2) _ _ _) = union (getFreeTypedVars e1) (getFreeTypedVars e2)
-- CS.LamC not implemented
-- CS.AppC not implemented
getFreeTypedVars (GenExpr (CS.If e1 _ e2 e3) _ _ _) = union (getFreeTypedVars e1) $ union (getFreeTypedVars e2) (getFreeTypedVars e3)
-- CS.MultiWayIf not implemented
getFreeTypedVars (GenExpr (CS.Member e _) _ _ _) = getFreeTypedVars e
-- CS.ArrayLit, CS.ArrayIndex, CS.ArrayMap2, CS.ArrayPut not implemented
getFreeTypedVars (GenExpr (CS.Tuple es) _ _ _) = nub $ concat $ map getFreeTypedVars es

getFreeTypedVars (GenExpr (CS.UnboxedRecord fs) _ _ _) = nub $ concat $ map (\(_,e) -> getFreeTypedVars e) fs
getFreeTypedVars (GenExpr (CS.Let bs e) _ _ _) = getFreeTypedVarsInLet bs e
getFreeTypedVars (GenExpr (CS.Put e fs) _ _ _) = union (getFreeTypedVars e) (nub $ concat $ map (\(_,e) -> getFreeTypedVars e) (catMaybes fs))
getFreeTypedVars (GenExpr (CS.Upcast e) _ _ _) = getFreeTypedVars e
-- CS.Annot not implemented
getFreeTypedVars _ = []

getBoundTypedVars :: GenIrrefPatn -> [TypedVar]
getBoundTypedVars (GenIrrefPatn (CS.PVar v) _ t) = [(TV v t)]
getBoundTypedVars (GenIrrefPatn (CS.PTuple ips) _ _) = nub $ concat $ map getBoundTypedVars ips
getBoundTypedVars (GenIrrefPatn (CS.PUnboxedRecord fs) _ _) = nub $ concat $ map (\(_,ip) -> getBoundTypedVars ip) (catMaybes fs)
getBoundTypedVars (GenIrrefPatn (CS.PTake pv fs) _ t) = 
    (TV pv $ mkTakeType True t (map fst (catMaybes fs))) : (nub $ concat $ map (\(_,ip) -> getBoundTypedVars ip) (catMaybes fs))
getBoundTypedVars (GenIrrefPatn (CS.PArray ips) _ _) = nub $ concat $ map getBoundTypedVars ips
getBoundTypedVars (GenIrrefPatn (CS.PArrayTake pv is) _ t) = 
    (TV pv $ mkArrTakeType True t (map fst is)) : (nub $ concat $ map (\(_,ip) -> getBoundTypedVars ip) is)
getBoundTypedVars _ = []

getFreeTypedVarsInAlt :: GenAlt -> [TypedVar]
getFreeTypedVarsInAlt (CS.Alt _ _ e) = getFreeTypedVars e

getFreeTypedVarsInLet :: [GenBnd] -> GenExpr -> [TypedVar]
getFreeTypedVarsInLet [] e = getFreeTypedVars e
getFreeTypedVarsInLet ((CS.Binding ip _ eb _) : bs) e = union (getFreeTypedVars eb) ((getFreeTypedVarsInLet bs e) \\ (getBoundTypedVars ip))
-- CS.BindingAlts not implemented

