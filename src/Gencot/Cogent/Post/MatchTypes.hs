{-# LANGUAGE PackageImports #-}
module Gencot.Cogent.Post.MatchTypes where

import Data.List (concatMap,nub,intersect,union,(\\),partition,find)
import qualified Data.Map as M
import Data.Maybe (catMaybes,isNothing,isJust)
import Data.Foldable (toList)

import Language.C.Data.Error
import Language.C.Analysis as LCA (Trav,recordError,modifyUserState)

import Cogent.Surface as CS
import Cogent.Common.Syntax as CCS

import Gencot.Cogent.Ast
import Gencot.Cogent.Error (typeMatch)
import Gencot.Cogent.Types (mkReadonly, isNonlinear, mayEscape, roCmpTypes, unbangType, getMemberType, getDerefType, getParamType)
import Gencot.Cogent.Bindings (errVar,replaceValVarType,replaceInGIP,mkDummyExpr)
import Gencot.Cogent.Expr (TypedVar(TV),namOfTV,mkUnitExpr)
import Gencot.Cogent.Post.Util (ETrav, runTravExpr, isValVar, freeInIrrefPatn, freeInBindings, boundInBindings)

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

{- Matching readonly subexpressions -}
{- to linear context: always error  -}
{------------------------------------}

roproc :: GenExpr -> ETrav GenExpr
roproc e = mapMExprOfGE roproc' e

roproc' :: ExprOfGE -> ETrav ExprOfGE
roproc' (CS.Let bs bdy) = do
    bs' <- roprocBindings bs bdy
    bdy' <- roproc bdy
    return $ CS.Let bs' bdy'
roproc' e = mapM roproc e

roprocBindings :: [GenBnd] -> GenExpr -> ETrav [GenBnd]
roprocBindings [] _ = return []
roprocBindings (b@(CS.Binding ip m e vs):bs) bdy =
    case exprOfGE e of
         CS.Var v | not $ isValVar v && (not $ mayEscape $ typOfGE e) ->
            case nonRoUseInLet v bs bdy of
                 Just t -> do
                   recordError $ typeMatch (orgOfGE e) ("readonly variable " ++ v ++ " used in linear context")
                   bs' <- roprocBindings (replaceValVarType t ip bs) bdy
                   return $ ((CS.Binding (replaceInGIP t ip) m (mkDummyExpr t ("readonly variable " ++ v ++ " used in linear context")) vs)
                             : bs')
                 Nothing -> do
                   bs' <- roprocBindings bs bdy
                   return (b : bs')

-- | Test whether a variable is used in a non-readonly way in an expression.
-- If no, the result is nothing, otherwise it returns the non-readonly type of the use.
nonRoUse :: CCS.VarName -> GenExpr -> Maybe GenType
nonRoUse v e =
    case exprOfGE e of
         CS.Let bs bdy -> nonRoUseInLet v bs bdy
         CS.App f arg _ -> nonRoUseInApp v (getParamType $ typOfGE f) $ exprOfGE arg
         _ -> Nothing

-- | Variable use as parameter in a function application
nonRoUseInApp :: CCS.VarName -> GenType -> ExprOfGE -> Maybe GenType
nonRoUseInApp v pt (CS.Var w) | v == w = if isNonlinear pt then Nothing else Just pt
nonRoUseInApp v pt (CS.Tuple es) =
    case typeOfGT pt of
         CS.TTuple pts -> case filter (\(e,t) -> e == CS.Var v) $ zip (map exprOfGE es) pts of
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
                CS.PTake _ [Just (_,fip)] | (CS.PVar cv) <- irpatnOfGIP fip ->
                  case exprOfGE e of
                       CS.Var w | w == v ->
                         if (not $ isModified cv (mkReadonly $ typOfGIP fip) bs) && (isNothing $ nonRoUseInLet cv bs bdy)
                            then Nothing
                            else Just $ unbangType $ typOfGE e
                              -- may not be correct for cv, but type of cv is never compared with corresponding component type
                       _ -> Nothing
                CS.PTuple [atk,_] | (CS.PArrayTake pv [(_,eip)]) <- irpatnOfGIP atk, (CS.PVar cv) <- irpatnOfGIP eip ->
                  case exprOfGE e of
                       CS.Tuple [ea,_] | (CS.Var w) <- exprOfGE ea, w == v ->
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
         CS.PVar pv -> Just $ TV pv $ typOfGIP ip
         _ -> Nothing
boundTo v (ip,CS.Var w) = Nothing
boundTo v (ip,CS.Tuple es) =
    case irpatnOfGIP ip of
         CS.PTuple ips -> let sub = catMaybes $ map (boundTo v) $ zip ips (map exprOfGE es)
                       in if null sub then Nothing else Just $ head sub
         _ -> Nothing
boundTo v (ip,CS.If _ _ e1 e2) =
    let r1 = boundTo v (ip,exprOfGE e1)
    in if isJust r1 then r1 else boundTo v (ip,exprOfGE e2)
boundTo v (ip,CS.Let bs e) =
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
isModified v t ((CS.Binding ip _ _ _):bs) | (CS.PTake pv [Just (fnam,fip)]) <- irpatnOfGIP ip, pv == v,
                                            (CS.PVar cv) <- irpatnOfGIP fip =
    isModified cv (getMemberType fnam t) bs || needToTake cv fnam t bs
isModified v t ((CS.Binding ip _ _ _):bs) | (CS.PTuple [atk,_]) <- irpatnOfGIP ip, (CS.PArrayTake pv [(_,eip)]) <- irpatnOfGIP atk, pv == v,
                                            (CS.PVar cv) <- irpatnOfGIP eip =
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

bangproc :: GenExpr -> ETrav GenExpr
bangproc e = mapMExprOfGE bangproc' e

-- | Try to bang subexpressions where that is possible.
bangproc' :: ExprOfGE -> ETrav ExprOfGE
bangproc' (CS.Let bs bdy) = do
    bsb <- bangprocInLet bs bdy
    bdyp <- bangproc bdy
    return $ CS.Let bsb bdyp
bangproc' (CS.If e [] e1 e2) = do
    (eb,bvs) <- runTravExpr [] $ tryBang e
    -- type of eb is always escapeable because it is boolean
    e1p <- bangproc e1
    e2p <- bangproc e2
    return $ CS.If eb bvs e1p e2p
-- No bang tried in CS.Match, CS.LamC, CS.MultiWayIf, because these are not generated.
bangproc' e = mapM bangproc e

bangprocInLet :: [GenBnd] -> GenExpr -> ETrav [GenBnd]
bangprocInLet [] _ = return []
bangprocInLet bs bdy = do
    (bb : bsr) <- tryBangBindings bs bdy
    bsrp <- bangprocInLet bsr bdy
    return (bb : bsrp)

-- | Try to bang variables in a prefix of a binding sequence.
-- The shortest prefix is used for which the result is escapeable.
-- If successful, the prefix is converted to a single binding with banged variables.
-- This binding binds (only) the variables which occur free in the remaining bindings followed by the expression.
-- Otherwise the sequence is returned unmodified.
tryBangBindings :: [GenBnd] -> GenExpr -> ETrav [GenBnd]
tryBangBindings [] _ = return []
tryBangBindings (b@(CS.Binding ip m e []):bs) bdy = do
    (eb,bvs) <- runTravExpr [] $ tryBang e
    if null bvs || (mayEscape $ typOfGE eb)
       then do
           bsb <- tryBangBindings bs bdy
           return ((CS.Binding ip m eb bvs) : bsb)
       else if null bs
       then do
           berr <- bangError b bvs eb
           return [berr]
       else tryBangBindings (combineBindings b (head bs) (tail bs) bdy) bdy

-- | Handle a binding as a banging error.
-- The bound expression could be made type correct by banging the variables in the list,
-- but the resulting expression has no escapeable type.
-- The third argument is the bound expression after banging the types of all variabes in the list.
-- If it is the same as in the original binding, all variable occurreces are replaced by dummies,
-- otherwise the expression is replaced as a whole by a dummy.
-- Additionally for each dummy an error is recorded.
bangError :: GenBnd -> [CCS.VarName] -> GenExpr -> ETrav GenBnd
-- TODO
bangError b bvs eb = return b

-- | Combine two bindings to a single binding
-- which binds the variables occurring free in a binding list followed by an expression.
-- The result is the binding list with the combined binding prepended.
combineBindings :: GenBnd -> GenBnd -> [GenBnd] -> GenExpr -> [GenBnd]
-- TODO
combineBindings b1 b2 bs bdy = bs

-- | Resolve readonly type incompatibilities in an expression by banging variables.
-- The result is the expression with resolved incompatibilities.
-- Additionally the monadic state contains the set of variable names which must be banged
-- to change the expression accordingly.
-- If there are readonly type incompatibilities which cannot be resolved by banging variables
-- they are resolved by using dummy expressions or the error variable and recording corresponding errors.
tryBang :: GenExpr -> Trav [CCS.VarName] GenExpr
tryBang e = tryBangVars [] e

-- | Try to change variable types as specified in a list of typed variables.
-- Resulting readonly type incompatibilities for other variables are resloved by changing
-- their type to the banged type. All other incompatibilities are resolved by replacing
-- expressions by dummy expressions or replacing bound variables by the error variable
-- with errors recorded.
-- The result is the changed expression without any readonly type incompatibilities.
-- The monadic state contains the set of variable names for which the type has been changed.
tryBangVars :: [TypedVar] -> GenExpr -> Trav [CCS.VarName] GenExpr
tryBangVars vs e = do
    modifyUserState (\s -> union (map namOfTV vs) s)
    (eb,bvs) <- runTravExpr [] $ rslvRoDiffs vs [] M.empty e
    if null bvs
       then return eb
       else tryBangVars bvs eb

-- | Resolve readonly type incompatibilities after changing the type of variables.
-- The first argument is a list of variables with their new types.
-- The second argument is a list of variables which may not be modified after the change.
-- The third argument is a map from value variables to the bound expression and
-- from component variables to the outermost container expression.
-- The result is the expression with changed types for the variables.
-- Additionally the monadic state contains the set of additional variables to be banged
-- for resolving readonly type incompatibilities, as variables typed by the banged type.
-- All other readonly type incompatibilities are resolved by replacing the incompatible subexpression
-- by a dummy expression and recording an error.
-- Bindings to a variable in the second list are replaced by bindings to the error variable
-- and an error is recorded.
rslvRoDiffs :: [TypedVar] -> [CCS.VarName] -> (M.Map CCS.VarName GenExpr) -> GenExpr -> Trav [TypedVar] GenExpr
rslvRoDiffs vs cvs vmap e@(GenExpr (CS.Var v) o t s) = do
    case find (\tv -> namOfTV tv == v)  vs of
         Nothing -> return e
         Just (TV vn vt) -> return $ GenExpr (CS.Var vn) o vt s
rslvRoDiffs vs cvs vmap e@(GenExpr (CS.PrimOp op es) o t s) = do
    esb <- mapM (rslvRoDiffs vs cvs vmap) es
    return $ GenExpr (CS.PrimOp op esb) o t s
rslvRoDiffs vs cvs vmap e@(GenExpr (CS.If e0 bvs e1 e2) o t s) = do
    e0b <- rslvRoDiffs vs cvs vmap e0
    e1b <- rslvRoDiffs vs cvs vmap e1
    e2b <- rslvRoDiffs vs cvs vmap e2
    (e1bm,e2bm,tm) <- matchRoDiffs vmap e1b e2b
    return $ GenExpr (CS.If e0b bvs e1bm e2bm) o tm s
rslvRoDiffs vs cvs vmap e@(GenExpr e' o t s) = do
    eb' <- rslvRoDiffs' vs cvs vmap e'
    return $ GenExpr eb' o (retypeExpr' eb') s

recordVariable :: TypedVar -> Trav [TypedVar] ()
recordVariable v = modifyUserState (\tvs -> if elem v tvs then tvs else v:tvs)

rslvRoDiffs' :: [TypedVar] -> [CCS.VarName] -> (M.Map CCS.VarName GenExpr) -> ExprOfGE -> Trav [TypedVar] ExprOfGE
-- TODO
rslvRoDiffs' vs cvs vmp e = return e

retypeExpr' :: ExprOfGE -> GenType
retypeExpr' e' = unitType

-- | Resolve readonly type incompatiilities between two expressions.
-- The first argument is a map from value variables to the bound expression and
-- from component variables to the outermost container expression.
-- If in the two resulting expressions the variables are retyped according to the resulting monadic state
-- they both have a type which is readonly compatible to the resulting type.
matchRoDiffs :: (M.Map CCS.VarName GenExpr) -> GenExpr -> GenExpr -> Trav [TypedVar] (GenExpr,GenExpr,GenType)
-- TODO
matchRoDiffs vmp e1 e2 | roCmpTypes (typOfGE e1) (typOfGE e2) = return (e1,e2,typOfGE e1)
matchRoDiffs vmp e1@(GenExpr (CS.If ec bvs et ee) o t s) e2 = do
    (e2mt,etm2,tt) <- matchRoDiffs vmp e2 et
    (e2me,eem2,te) <- matchRoDiffs vmp e2 ee
    -- ???
    return (e1,e2,typOfGE e1)
matchRoDiffs vmp e1 e2 = return $ (e1,e2,typOfGE e1)

{-
-- | Replace variable types in an expression.
-- For every occurrence of a variable from the list in the expression its type is replaced by the type in the list.
-- That type is also transferred to all affected value variables.
replaceVarTypes :: [TypedVar] -> GenExpr -> GenExpr
replaceVarTypes vs e = e

-- | Try banging the variables in an expression.
-- The list contains the variables with their banged types.
-- If after replacing the types in the expression all readonly type matches are ok, the resulting expression is returned.
-- Otherwise, if the match was not prevented by variables only, Nothing is returned.
-- Otherwise the set of variables which prevented a match is returned as a hint to try banging them as well.
tryBang :: [TypedVar] -> GenExpr -> Either GenExpr (Option [TypedVar])
tryBang vs e =
    rotest $ replaceVarTypes vs e
    -}
