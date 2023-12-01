{-# LANGUAGE PackageImports #-}
module Gencot.Cogent.Post.Misc where

import Data.List (intercalate,transpose,concatMap,foldl1',isPrefixOf,nub,intersect,union,(\\),partition,find,zipWith,zip3, zip4)
import Data.Maybe (catMaybes,isNothing,isJust,fromJust)

import Language.C.Data.Error
import Language.C.Analysis as LCA (Trav,recordError,getUserState,modifyUserState)

import Cogent.Surface as CS
import Cogent.Common.Syntax as CCS

import Gencot.Names (mapNull)
import Gencot.Cogent.Ast
import Gencot.Cogent.Error (typeMatch)
import Gencot.Cogent.Types (
  mkFunType, isReadonly, getParamType, getResultType)
import Gencot.Cogent.Expr (
  TypedVar(TV), typOfTV, mkUnitExpr, mkVarExpr, mkTopLevelFunExpr, mkAppExpr, mkLetExpr)
import Gencot.Cogent.Bindings (errVar, mkVarBinding)
import Gencot.Cogent.Post.Util (ETrav, isPutExpr)

{- Modification of Readonly Containers -}
{- Detect and record errors.           -}
{---------------------------------------}

romodproc :: GenExpr -> ETrav GenExpr
romodproc e = romodprocVars [] e

-- | Check component variables for being modified.
-- The first argument is a set of component variables which must not be modified.
-- In the expression, additional component variables may not be modified if they are taken from a readonly container.
-- Modified variables are replaced by the error variable in their binding.
-- All types remain unchanged.
romodprocVars :: [CCS.VarName] -> GenExpr -> ETrav GenExpr
romodprocVars cvs e = mapMExprOfGE (romodprocVars' cvs) e

romodprocVars' :: [CCS.VarName] -> ExprOfGE -> ETrav ExprOfGE
romodprocVars' cvs e@(CS.Let _ _) = romodprocInLet cvs e
romodprocVars' cvs e = mapM (romodprocVars cvs) e

romodprocInLet :: [CCS.VarName] -> ExprOfGE -> ETrav ExprOfGE
romodprocInLet cvs (CS.Let [] bdy) = do
    bdyr <- romodprocVars cvs bdy
    return $ CS.Let [] bdyr
romodprocInLet cvs (CS.Let ((CS.Binding ip m e bvs) : bs) bdy) = do
    er <- romodprocVars cvs e
    (ipr,cvs') <- romodprocPattern cvs ip $ isPutExpr $ exprOfGE e
    (CS.Let bsr bdyr) <- romodprocInLet cvs' (CS.Let bs bdy)
    return $ CS.Let ((CS.Binding ipr m er bvs) : bsr) bdyr

romodprocPattern :: [CCS.VarName] -> GenIrrefPatn -> [Bool] -> ETrav (GenIrrefPatn, [CCS.VarName])
romodprocPattern cvs ip@(GenIrrefPatn (CS.PTake pv [Just (_,(GenIrrefPatn (CS.PVar cv) _ _))]) _ t) _ =
    return (ip, if (isReadonly t) || (elem pv cvs) then union cvs [cv] else cvs)
romodprocPattern cvs ip@(GenIrrefPatn (CS.PArrayTake pv [(_,(GenIrrefPatn (CS.PVar cv) _ _))]) _ t) _ =
    return (ip, if (isReadonly t) || (elem pv cvs) then union cvs [cv] else cvs)
romodprocPattern cvs (GenIrrefPatn (CS.PTuple ips) o t) ispts = do
    ipcvss <- mapM (\(ip,ispt) -> romodprocPattern cvs ip [ispt]) $ zip ips ispts
    let (ipsr,cvss) = unzip ipcvss
    return (GenIrrefPatn (CS.PTuple ipsr) o t, nub $ concat cvss)
romodprocPattern cvs (GenIrrefPatn (CS.PVar pv) o t) [False] | elem pv cvs = do
    recordError $ typeMatch o "Component of readonly struct modified"
    return (GenIrrefPatn (CS.PVar errVar) o t, cvs)
romodprocPattern cvs ip _ = return (ip,cvs)

{- Process mayNull, notNull -}
{- and cogent_NULL          -}
{----------------------------}

opnullproc :: GenExpr -> GenExpr
opnullproc e = opnullToReadonly $ bindToNullInNothing e

-- | Convert mayNull and notNull to readonly if needed and convert cogent_NULL to null or roNull.
opnullToReadonly :: GenExpr -> GenExpr
opnullToReadonly (GenExpr (CS.Var v) o t c) | v == mapNull =
    mkAppExpr (mkTopLevelFunExpr (nullFun, mkFunType unitType t) []) $ mkUnitExpr
    where nullFun = if isReadonly t
                      then "roNull"
                      else "null"
opnullToReadonly (GenExpr (CS.App (GenExpr (CS.TLApp f mt ml il) fo ft fc) e x) o t c)
    | elem f ["mayNull","notNull"] && (isReadonly $ getParamType ft) =
    GenExpr (CS.App (GenExpr (CS.TLApp rof mt ml il) fo ft fc) (opnullToReadonly e) x) o t c
    where rof = if f == "mayNull"
                  then "roMayNull"
                  else "roNotNull"
opnullToReadonly e = mapExprOfGE (fmap opnullToReadonly) e

-- | For every nothing-branch of a NULL test bind the tested variable to cogent_NULL.
-- This prevents double use if the variable has linear type.
-- We assume that only match expressions exist which have been created by convVarNullTest.
bindToNullInNothing :: GenExpr -> GenExpr
bindToNullInNothing (GenExpr (CS.Match e0@(GenExpr (CS.App _ (GenExpr (CS.Var v) _ vt _) _) _ _ _) bvs [aNothing, aSome]) o t c) =
    GenExpr (CS.Match e0 bvs [CS.Alt p l $ bindToNullInExpr (TV v vt) e, aSome']) o t c
    where (CS.Alt p l e) = bindToNullInAlt aNothing
          aSome' = bindToNullInAlt aSome
bindToNullInNothing e = mapExprOfGE (fmap bindToNullInNothing) e

bindToNullInAlt :: GenAlt -> GenAlt
bindToNullInAlt (CS.Alt p l e) = CS.Alt p l $ bindToNullInNothing e

bindToNullInExpr :: TypedVar -> GenExpr -> GenExpr
bindToNullInExpr tv (GenExpr (CS.Let bs bdy) o t c) =
    GenExpr (CS.Let ((mkVarBinding tv $ mkVarExpr $ TV mapNull $ typOfTV tv) : bs) bdy) o t c
bindToNullInExpr tv e =
    mkLetExpr [mkVarBinding tv $ mkVarExpr $ TV mapNull $ typOfTV tv] e

