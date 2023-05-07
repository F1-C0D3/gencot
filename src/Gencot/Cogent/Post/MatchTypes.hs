{-# LANGUAGE PackageImports #-}
module Gencot.Cogent.Post.MatchTypes where

import Data.List (concatMap,nub,intersect,union,(\\),partition,find)
import qualified Data.Map as M
import Data.Maybe (catMaybes,isNothing,isJust)
import Data.Foldable (toList)

import Cogent.Surface as CS
import Cogent.Common.Syntax as CCS

import Gencot.Cogent.Ast
import Gencot.Cogent.Types (mkReadonly, isNonlinear, unbangType, getMemberType, getDerefType, getParamType)
import Gencot.Cogent.Expr (TypedVar(TV))
import Gencot.Cogent.Post.Util (isValVar, freeInIrrefPatn, freeInBindings, boundInBindings)

{- Matching readonly subexpressions -}
{- to linear context: always error  -}
{------------------------------------}

-- Assumption for all expressions:
-- - expressions bound in a binding are only
--   literals, variables, tuples, constant or function names, function applications, operator applications,
--   put/array-put, conditional expressions, let-expressions
-- - branches in conditional expressions, the argument of a function application, and the body of a let-expresson
--   is a single variable or a tuple of variables.
-- - all other sub-expressions are single variables.
-- Assumptions for all patterns:
-- - irrefutable patterns in a binding are only
--   variables, tuples, wildcard, take, or array-take
-- - subpatterns in tuples are only variables or wildcards, or the tuple is a pair of an array-take and a variable.
--   array-takes only occur in such pairs.
-- - a take or array-take has exactly one taken field or element

roproc :: GenExpr -> GenExpr
-- TODO
roproc e = e

-- | Test whether a variable is used in a non-readonly way in an expression.
-- If no, the result is nothing, otherwise it returns the non-readonly type of the use.
nonRoUse :: CCS.VarName -> GenExpr -> Maybe GenType
nonRoUse v e =
    case exprOfGE e of
         Let bs bdy -> nonRoUseInLet v bs bdy
         App f arg _ -> nonRoUseInApp v (getParamType $ typOfGE f) $ exprOfGE arg
         _ -> Nothing

-- | Variable use as parameter in a function application
nonRoUseInApp :: CCS.VarName -> GenType -> ExprOfGE -> Maybe GenType
nonRoUseInApp v pt (Var w) | v == w = if isNonlinear pt then Nothing else Just pt
nonRoUseInApp v pt (Tuple es) =
    case typeOfGT pt of
         TTuple pts -> case filter (\(e,t) -> e == Var v) $ zip (map exprOfGE es) pts of
                            [] -> Nothing
                            (_,t):_ -> if isNonlinear t then Nothing else Just t
         _ -> Nothing

-- | Variable use in binding sequence with body expression
nonRoUseInLet :: CCS.VarName -> [GenBnd] -> GenExpr -> Maybe GenType
nonRoUseInLet v [] bdy = nonRoUse v bdy
nonRoUseInLet v ((CS.Binding ip _ e _):bs) bdy =
    case nonRoUse v e of
         Just t -> Just t
         Nothing ->
           case irpatnOfGIP ip of
                PTake _ [Just (_,fip)] | (PVar cv) <- irpatnOfGIP fip ->
                  case exprOfGE e of
                       Var w | w == v ->
                         if (not $ isModified cv (mkReadonly $ typOfGIP fip) bs) && (isNothing $ nonRoUseInLet cv bs bdy)
                            then Nothing
                            else Just $ unbangType $ typOfGE e
                              -- may not be correct for cv, but type of cv is never compared with corresponding component type
                       _ -> Nothing
                PTuple [atk,_] | (PArrayTake pv [(_,eip)]) <- irpatnOfGIP atk, (PVar cv) <- irpatnOfGIP eip ->
                  case exprOfGE e of
                       Tuple [ea,_] | (Var w) <- exprOfGE ea, w == v ->
                         if (not $ isModified cv (mkReadonly $ typOfGIP eip) bs) && (isNothing $ nonRoUseInLet cv bs bdy)
                            then Nothing
                            else Just $ unbangType $ typOfGE ea
                              -- may not be correct for cv, but type of cv is never compared with corresponding component type
                       _ -> Nothing
                _ ->
                  let chain =
                        case boundTo v (ip,exprOfGE e) of
                             Just (TV nm tp) -> -- the binding binds v to nm
                               if not $ isNonlinear tp -- check type of nm
                                  then Just tp
                                  else if isValVar nm
                                          then nonRoUseInLet nm bs bdy -- is nm used non-readonly in the rest?
                                          else Nothing
                             Nothing -> Nothing
                  in if isJust chain
                        then chain
                        else if v `elem` (freeInIrrefPatn ip) -- v is re-bound in the binding
                                then Nothing
                                else nonRoUseInLet v bs bdy -- is v used non-readonly in the rest?

-- | The variable to which the given variable is bound in the binding of the expression to the pattern.
boundTo :: CCS.VarName -> (GenIrrefPatn,ExprOfGE) -> Maybe TypedVar
boundTo v (ip,Var w) | v == w =
    case irpatnOfGIP ip of
         PVar pv -> Just $ TV pv $ typOfGIP ip
         _ -> Nothing
boundTo v (ip,Var w) = Nothing
boundTo v (ip,Tuple es) =
    case irpatnOfGIP ip of
         PTuple ips -> let sub = catMaybes $ map (boundTo v) $ zip ips (map exprOfGE es)
                       in if null sub then Nothing else Just $ head sub
         _ -> Nothing
boundTo v (ip,If _ _ e1 e2) =
    let r1 = boundTo v (ip,exprOfGE e1)
    in if isJust r1 then r1 else boundTo v (ip,exprOfGE e2)
boundTo v (ip,Let bs e) =
    if v `elem` boundInBindings bs
       then Nothing
       else boundTo v (ip,exprOfGE e)
boundTo v _ = Nothing

-- | Test whether a component variable is modified in a sequence of bindings.
-- This is the case if either a value is bound to it (component is replaced)
-- or if it is used as container in a take which modifies the container (component is modified).
-- The second argument is the type considered for the component.
isModified :: CCS.VarName -> GenType -> [GenBnd] -> Bool
isModified v t [] = False
isModified v t ((CS.Binding ip _ _ _):bs) | (PTake pv [Just (fnam,fip)]) <- irpatnOfGIP ip, pv == v,
                                            (PVar cv) <- irpatnOfGIP fip =
    isModified cv (getMemberType fnam t) bs || needToTake cv fnam t bs
isModified v t ((CS.Binding ip _ _ _):bs) | (PTuple [atk,_]) <- irpatnOfGIP ip, (PArrayTake pv [(_,eip)]) <- irpatnOfGIP atk, pv == v,
                                            (PVar cv) <- irpatnOfGIP eip =
    isModified cv (getDerefType t) bs || needToTake cv "" t bs
isModified v t ((CS.Binding ip _ _ _):_) | v `elem` freeInIrrefPatn ip = True

-- | Test whether a component variable needs to be taken from its container.
-- This is the case if the container is linear and the component is nonlinear and its (old) value is used in the bindings
-- or if the container and the component are linear and the component is used or replaced in the bindings.
-- The second argument is the component field name for a record container or "" for an array container.
-- The third argument is the assumed type of the container.
needToTake :: CCS.VarName -> CCS.FieldName -> GenType -> [GenBnd] -> Bool
needToTake cv fn t bs | isNonlinear t = False
needToTake cv "" t bs | isNonlinear $ getDerefType t = cv `elem` freeInBindings bs
needToTake cv fn t bs | isNonlinear $ getMemberType fn t = cv `elem` freeInBindings bs
needToTake cv "" t bs = cv `elem` freeInBindings bs || isModified cv (getDerefType t) bs
needToTake cv fn t bs = cv `elem` freeInBindings bs || isModified cv (getMemberType fn t) bs

{- Matching linear subexpressions -}
{- to readonly context: try bang  -}
{----------------------------------}

bangproc :: GenExpr -> GenExpr
-- TODO
bangproc e = e
