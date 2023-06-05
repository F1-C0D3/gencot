{-# LANGUAGE PackageImports #-}
module Gencot.Cogent.Post.MatchTypes where

import Data.List (intercalate,concatMap,nub,intersect,union,(\\),partition,find,zipWith)
import qualified Data.Map as M
import Data.Maybe (catMaybes,isNothing,isJust)
import Data.Foldable (toList)

import Language.C.Data.Error
import Language.C.Analysis as LCA (Trav,recordError,modifyUserState)

import Cogent.Surface as CS
import Cogent.Common.Syntax as CCS

import Gencot.Cogent.Ast
import Gencot.Cogent.Error (typeMatch)
import Gencot.Cogent.Types (
  mkTupleType, mkReadonly,
  isNonlinear, isRegular, mayEscape, isReadonly, roCmpTypes, unbangType, getMemberType, getDerefType, getParamType, getResultType)
import Gencot.Cogent.Bindings (errVar, replaceValVarType, replaceInGIP, mkDummyExpr, toDummyExpr, mkVarTuplePattern)
import Gencot.Cogent.Expr (TypedVar(TV), namOfTV, mkUnitExpr, mkLetExpr, mkVarTupleExpr)
import Gencot.Cogent.Post.Util (
  ETrav, runExprTrav, isValVar, isCVar, freeInIrrefPatn, freeInBindings, freeUnderBinding, boundInBindings,
  getIPatternsList, getExprList)

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
{-
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
-}


{- Modification of Readonly Containers -}
{- Detect and record errors.           -}
{---------------------------------------}

romodproc :: GenExpr -> ETrav GenExpr
romodproc e = romodprocVars [] e

-- | Check component variables for being modified.
-- The first argument is a set of component variables which must not be modified.
-- In the expression, additional component variables may not be modified if they are taken from a readonly container.
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

-- | Whether an expression seen as tuple is a put expression.
isPutExpr :: ExprOfGE -> [Bool]
isPutExpr (CS.Put _ _) = [True]
isPutExpr (CS.ArrayPut _ _) = [True]
isPutExpr (CS.Tuple es) = concat $ map (isPutExpr . exprOfGE) es
isPutExpr (CS.If _ _ e1 e2) =
    -- mostly irrelevant because branches never contain put expressions,
    -- but must be mapped so that the list has the correct number of entries.
    map (\(b1,b2) -> b1 || b2) $ zip (isPutExpr $ exprOfGE e1) (isPutExpr $ exprOfGE e2)
isPutExpr (CS.Let _ bdy) = isPutExpr $ exprOfGE bdy
isPutExpr (CS.App f e _) = case typeOfGT $ getResultType $ typOfGE f of
                              CS.TTuple ts -> map (const False) ts
                              _ -> [False]
isPutExpr _ = [False]

{- Matching linear subexpressions -}
{- to readonly context: try bang  -}
{----------------------------------}

bangproc :: GenExpr -> ETrav GenExpr
bangproc e = mapMExprOfGE bangproc' e

-- | Try to bang subexpressions where that is possible.
bangproc' :: ExprOfGE -> ETrav ExprOfGE
bangproc' (CS.Let bs bdy) = do
    bsb <- bangprocInLet bs $ exprOfGE bdy
    bdyp <- bangproc bdy
    return $ CS.Let bsb bdyp
bangproc' (CS.If e [] e1 e2) = do
    (eb,bvs,errs) <- runExprTrav [] $ roDiffsBang e
    -- type of eb is always escapeable because it is boolean
    mapM recordError errs
    (ebe,bvse) <- if null errs then extendBang eb bvs else return (eb,bvs)
    e1p <- bangproc e1
    e2p <- bangproc e2
    return $ CS.If ebe bvse e1p e2p
-- No bang tried in CS.Match, CS.LamC, CS.MultiWayIf, because these are not generated.
bangproc' e = mapM bangproc e

-- | Resolve all readonly type incompatibilities.
-- In the monadic state a minimal set of variables is returned which must be banged.
-- Remaining incompatibiliteis are resolved using dummy expressions and the error variable,
-- returning corresponding error messages in the monadic state.
roDiffsBang :: GenExpr -> Trav [CCS.VarName] GenExpr
roDiffsBang e = do
    (eb,bvs,errs) <- runExprTrav [] $ bangInExpr e
    if (not $ null errs) && (hasInnerBangPositions $ exprOfGE e)
       then do
           (ep,(),errp) <- runExprTrav () $ bangproc e -- try to bang only parts of e
           mapM recordError errp
           return ep
       else do
           mapM recordError errs
           modifyUserState (\tvs -> union tvs bvs)
           return eb

-- | Does an expression contain syntactic possibilities for banging variables.
-- This is the case if it contains subexpressions of kind Let, If, Match, MultiWayIf.
-- Match and MultiWayIf are not checked because they are not generated.
hasInnerBangPositions :: ExprOfGE -> Bool
hasInnerBangPositions (CS.Let _ _) = True
hasInnerBangPositions (CS.If _ _ _ _) = True
hasInnerBangPositions (CS.PrimOp _ es) = any (hasInnerBangPositions . exprOfGE) es
hasInnerBangPositions (CS.Tuple es) = any (hasInnerBangPositions . exprOfGE) es
hasInnerBangPositions (CS.App e1 e2 _) = (hasInnerBangPositions $ exprOfGE e1) || (hasInnerBangPositions $ exprOfGE e2)
-- Put and ArrayPut are always generated with variables as subexpressions, therefore no inner bang positions.
hasInnerBangPositions _ = False

-- | Try to bang subexpressions in the bindings of a let expressions.
-- The let body is required to determine the variables used in it, it is not processed.
bangprocInLet :: [GenBnd] -> ExprOfGE -> ETrav [GenBnd]
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
tryBangBindings :: [GenBnd] -> ExprOfGE -> ETrav [GenBnd]
tryBangBindings [] _ = return []
tryBangBindings (b@(CS.Binding ip m e []):bs) bdy = do
    (eb,bvs,errs) <- runExprTrav [] $ roDiffsBang e
    if null bvs || (mayEscape $ typOfGE eb)
       then do
           mapM recordError errs
           (ebe,bvse) <- if null errs then extendBang eb bvs else return (eb,bvs)
           bsb <- tryBangBindings bs bdy
           let (inoro,enoro) = matchRoTypes (typOfGIP ip) (typOfGE ebe)
           if inoro == enoro
              then return ((CS.Binding ip m ebe bvse) : bsb)
              else if enoro then do
                  let bmsg = if null bvs then "L" else "After banging variable(s) " ++ (intercalate ", " bvs) ++ " l"
                  let msg = bmsg ++ "inear expression is used in readonly context"
                  recordError $ typeMatch (orgOfGIP ip) msg
                  return ((CS.Binding ip m (toDummyExpr ebe $ mkDummyExpr (typOfGIP ip) msg) bvse) : bsb)
              else do
                  let msg = "Readonly expression is used in linear context"
                  recordError $ typeMatch (orgOfGIP ip) msg
                  return ((CS.Binding ip m (toDummyExpr ebe $ mkDummyExpr (typOfGIP ip) msg) bvse) : bsb)
       else if null bs
       then do
           mapM recordError errs
           let msg = "Necessary banging of variables " ++ (intercalate ", " bvs) ++ " leads to non-escapeable type"
           recordError $ typeMatch (orgOfGIP ip) msg
           if roCmpTypes (typOfGIP ip) (typOfGE eb)
              then return $ [CS.Binding ip m (bangToError bvs eb) bvs]
              else return $ [CS.Binding ip m (toDummyExpr eb $ mkDummyExpr (typOfGIP ip) msg) []]
       else tryBangBindings (combineBindings b (head bs) (tail bs) bdy) bdy

-- | Replace all occurrences of variables in a set by dummy expressions.
bangToError :: [CCS.VarName] -> GenExpr -> GenExpr
bangToError vs e = mapExprOfGE (bangToError' vs (typOfGE e)) e

bangToError' :: [CCS.VarName] -> GenType -> ExprOfGE -> ExprOfGE
bangToError' vs t e@(CS.Var v) =
    if elem v vs
       then exprOfGE $ mkDummyExpr t ("Necessary banging of " ++ v ++ " leads to non-escapeable type")
       else e
bangToError' vs _ e = fmap (bangToError vs) e

-- | Combine two bindings to a single binding
-- which binds the variables occurring free in a binding list followed by an expression.
-- The result is the binding list with the combined binding prepended.
combineBindings :: GenBnd -> GenBnd -> [GenBnd] -> ExprOfGE -> [GenBnd]
combineBindings b1@(CS.Binding ip1 _ _ _) b2@(CS.Binding ip2 _ _ _) bs bdy =
    (CS.Binding (mkVarTuplePattern tvs) Nothing (mkLetExpr [b1,b2] (mkVarTupleExpr tvs)) []):bs
    where vs = intersect (boundInBindings [b1, b2]) (freeUnderBinding bs bdy)
          tvs = map (addTypeFromPatterns ((getIPatternsList ip2) ++ (getIPatternsList ip1))) vs

addTypeFromPatterns :: [GenIrrefPatn] -> CCS.VarName -> TypedVar
addTypeFromPatterns [] v = TV v unitType
addTypeFromPatterns ((GenIrrefPatn (CS.PVar pv) _ t):ips) v | pv == v = TV v t
addTypeFromPatterns (_:ips) v = addTypeFromPatterns ips v

-- | Resolve readonly type incompatibilities in an expression by banging variables.
-- The result is the expression with resolved incompatibilities.
-- Additionally the monadic state contains the set of variable names which must be banged
-- to change the expression accordingly.
-- If there are readonly type incompatibilities which cannot be resolved by banging variables
-- they are resolved by using dummy expressions or the error variable and recording corresponding errors.
bangInExpr :: GenExpr -> Trav [CCS.VarName] GenExpr
bangInExpr e = bangVars [] e

-- | Bang the types at every occurrence of variables in the given list.
-- Resulting readonly type incompatibilities for other variables are resolved
-- by banging their types at every occurrence as well.
-- All other incompatibilities are resolved by replacing expressions by dummy expressions
-- or replacing bound variables by the error variable with errors recorded.
-- The result is the changed expression where all readonly type incompatibilities have been resolved.
-- In the monadic state the set of all variables is returned for which the type has been banged.
bangVars :: [CCS.VarName] -> GenExpr -> Trav [CCS.VarName] GenExpr
bangVars vs e = do
    modifyUserState (\s -> union vs s)
    (eb,bvs,errs) <- runExprTrav [] $ rslvRoDiffs vs [] M.empty e
    mapM recordError errs
    if null bvs
       then return eb
       else bangVars bvs eb

-- | Try to bang additional variables in an expression.
-- Candidates are all free variables which occur as container with linear type in a take operation.
-- The result is the expression with additional types banged and the extended set of variables to bang.
extendBang :: GenExpr -> [CCS.VarName] -> ETrav (GenExpr, [CCS.VarName])
extendBang e vs = do
    (eb,bvs) <- extendBangVars e $ getBangCandidates [] e
    return (eb,union vs bvs)

-- | Try to change variable types in an expression according to a list of typed variables.
-- The result is the modified expression together with the list of all variables
-- where the type has been successfully changed.
extendBangVars :: GenExpr -> [CCS.VarName] -> ETrav (GenExpr, [CCS.VarName])
extendBangVars e [] = return (e,[])
extendBangVars e (v:vs) = do
    (eb,bvs,errs) <- runExprTrav [] $ bangVars [v] e
    if null errs && (mayEscape $ typOfGE eb)
       then do
           (ebb,bbvs) <- extendBangVars eb (vs \\ bvs)
           return (ebb, union bbvs bvs)
       else extendBangVars e vs

-- | Return all free variables which occur as container with linear type in a take operation.
-- The first argument is the list of all variables not free in the expression.
getBangCandidates :: [CCS.VarName] -> GenExpr -> [CCS.VarName]
getBangCandidates bvs (GenExpr (CS.Let bs bdy) _ _ _) =
    union (getBangCandInBindings bvs bs) (getBangCandidates (boundInBindings bs) bdy)
getBangCandidates bvs e = nub $ concat $ fmap (getBangCandidates bvs) $ exprOfGE e

-- | Return all free variables which occur as container with linear type in a take operation.
-- The first argument is the list of all variables not free in the bindings.
getBangCandInBindings :: [CCS.VarName] -> [GenBnd] -> [CCS.VarName]
getBangCandInBindings _ [] = []
getBangCandInBindings bvs ((CS.Binding ip _ e _):bs) =
    union (union (getBangCandInPattern bvs ip) (getBangCandidates bvs e)) $ getBangCandInBindings (union bvs $ freeInIrrefPatn ip) bs

-- | Return all free variables which occur as container with linear type in a take operation.
-- The first argument is the list of all variables not free in the bound expression.
getBangCandInPattern :: [CCS.VarName] -> GenIrrefPatn -> [CCS.VarName]
getBangCandInPattern bvs (GenIrrefPatn (CS.PTake pv [Just (_,(GenIrrefPatn (CS.PVar cv) _ _))]) _ t)
    | (not $ elem pv bvs) && (not $ isNonlinear t) = [pv]
getBangCandInPattern bvs (GenIrrefPatn (CS.PArrayTake pv [(_,(GenIrrefPatn (CS.PVar cv) _ _))]) _ t)
    | (not $ elem pv bvs) && (not $ isNonlinear t) = [pv]
getBangCandInPattern bvs (GenIrrefPatn (CS.PTuple ips) _ _) = nub $ concat $ map (getBangCandInPattern bvs) ips
getBangCandInPattern _ _ = []

-- | Variable source map.
-- It maps value variables and component variables to their set of source variables.
-- These are the C variables which must be banged to bang the type of the value/component variable.
-- For a component variable it is a variable for the outermost container, if existent.
-- A variable may have more than one source variable if it is the result of a conditional expression.
-- If a variable is mapped to the empty set its type cannot be banged.
type VarSourceMap = M.Map CCS.VarName [CCS.VarName]

getVarSources :: VarSourceMap -> CCS.VarName -> [CCS.VarName]
getVarSources vmap v | isCVar v = [v]
getVarSources vmap v = M.findWithDefault [] v vmap

recordSources :: VarSourceMap -> CCS.VarName -> Trav [CCS.VarName] ()
recordSources vmap v = modifyUserState (\tvs -> union tvs $ getVarSources vmap v)

-- | Source variables of an expression.
-- If the expression has a tuple type return the list of source variable sets for all components.
-- Otherwise return a singleton list.
getExprSources :: VarSourceMap -> ExprOfGE -> [[CCS.VarName]]
getExprSources vmap (CS.Var v) = [getVarSources vmap v]
getExprSources vmap (CS.If _ _ e1 e2) = zipWith union (getExprSources vmap $ exprOfGE e1) (getExprSources vmap $ exprOfGE e2)
getExprSources vmap (CS.Tuple es) = concatMap ((getExprSources vmap) . exprOfGE) es
getExprSources vmap (CS.Put e pts) = getExprSources vmap $ exprOfGE e
getExprSources vmap (CS.ArrayPut e pts) = getExprSources vmap $ exprOfGE e
getExprSources vmap (CS.Let bs bdy) = getExprSources (addVarSourcesFromBindings vmap bs) $ exprOfGE bdy
getExprSources _ _ = [[]]

addVarSourcesFromBindings :: VarSourceMap -> [GenBnd] -> VarSourceMap
addVarSourcesFromBindings vmap [] = vmap
addVarSourcesFromBindings vmap ((CS.Binding ip _ e _):bs) =
    addVarSourcesFromBindings (addVarSourcesFromBinding vmap (ip,getExprSources vmap $ exprOfGE e)) bs

addVarSourcesFromBinding :: VarSourceMap -> (GenIrrefPatn,[[CCS.VarName]]) -> VarSourceMap
addVarSourcesFromBinding vmap (GenIrrefPatn (CS.PVar pv) _ t, [ess])
    | (isValVar pv) && (not $ isRegular t) = M.insert pv ess vmap
addVarSourcesFromBinding vmap (GenIrrefPatn (CS.PTuple ps) _ t, esss) | not $ isRegular t =
    M.unions $ map (\(ip,ess) -> addVarSourcesFromBinding vmap (ip,[ess])) $ zip ps esss
addVarSourcesFromBinding vmap (GenIrrefPatn (CS.PTake pv [Just (_,(GenIrrefPatn (CS.PVar cv) _ _))]) _ t, [ess])
    | not $ isRegular t = M.insert cv ess vmap
addVarSourcesFromBinding vmap (GenIrrefPatn (CS.PArrayTake pv [(_,(GenIrrefPatn (CS.PVar cv) _ _))]) _ t, [ess])
    | not $ isRegular t = M.insert cv ess vmap
addVarSourcesFromBinding vmap _ = vmap

-- | Bang variable types and resolve readonly type incompatibilities in an expression.
-- The first argument is a list of variables for which the type must be banged at every occurrence.
-- The second argument is a list of variables which may not be modified after the change.
-- The third argument is the variable source map for all variables of linear type bound in the context.
-- The result is the expression with changed types for the variables.
-- Additionally the monadic state contains the set of additional variables to be banged
-- for resolving readonly type incompatibilities.
-- All other readonly type incompatibilities are resolved by replacing the incompatible subexpression
-- by a dummy expression and recording an error.
-- Bindings to a variable in the second list are replaced by bindings to the error variable
-- and an error is recorded.
rslvRoDiffs :: [CCS.VarName] -> [CCS.VarName] -> VarSourceMap -> GenExpr -> Trav [CCS.VarName] GenExpr
rslvRoDiffs vs cvs vmap e@(GenExpr (CS.Var v) o t s) =
    if not $ null $ intersect vs $ getVarSources vmap v
       then return $ GenExpr (CS.Var v) o (mkReadonly t) s
       else return e
rslvRoDiffs vs cvs vmap (GenExpr (CS.If e0 bvs e1 e2) o t s) = do
    e0b <- rslvRoDiffs vs cvs vmap e0
    e1b <- rslvRoDiffs vs cvs vmap e1
    e2b <- rslvRoDiffs vs cvs vmap e2
    (e1bm,e2bm,tm) <- matchRoExprs vmap e1b e2b
    return $ GenExpr (CS.If e0b bvs e1bm e2bm) o tm s
rslvRoDiffs vs cvs vmap (GenExpr (CS.App f e infx) o t s) = do
    eb <- rslvRoDiffs vs cvs vmap e
    ebm <- matchRoExpr vmap (getParamType $ typOfGE f) eb
    return $ GenExpr (CS.App f ebm infx) o t s
rslvRoDiffs vs cvs vmap (GenExpr (CS.Let bs bdy) o t s) = do
    (bsb,bdyb) <- rslvRoDiffsInLet vs cvs vmap bs bdy
    return (GenExpr (CS.Let bsb bdyb) o (typOfGE bdyb) s)
rslvRoDiffs vs cvs vmap (GenExpr (CS.Tuple es) o t s) = do
    esb <- mapM (rslvRoDiffs vs cvs vmap) es
    return $ GenExpr (CS.Tuple esb) o (mkTupleType $ map typOfGE esb) s
rslvRoDiffs vs cvs vmap (GenExpr (CS.Put ec [Just (f,ev)]) o t s) = do
    ecb <- rslvRoDiffs vs cvs vmap ec
    evb <- rslvRoDiffs vs cvs vmap ev
    return (GenExpr (CS.Put ecb [Just (f,evb)]) o (typOfGE ecb) s)
rslvRoDiffs vs cvs vmap (GenExpr (CS.ArrayPut ec [(i,ev)]) o t s) = do
    ecb <- rslvRoDiffs vs cvs vmap ec
    -- i is an index variable and thus not affected by banging
    evb <- rslvRoDiffs vs cvs vmap ev
    return (GenExpr (CS.ArrayPut ecb [(i,evb)]) o (typOfGE ecb) s)
rslvRoDiffs vs cvs vmap e =
    mapMExprOfGE (mapM (rslvRoDiffs vs cvs vmap)) e

-- | Bang variable types and resolve readonly type incompatibilities in a binding sequence and a body expression.
-- Works as for rslvRoDiffs.
rslvRoDiffsInLet :: [CCS.VarName] -> [CCS.VarName] -> VarSourceMap -> [GenBnd] -> GenExpr -> Trav [CCS.VarName] ([GenBnd],GenExpr)
rslvRoDiffsInLet vs cvs vmap [] bdy = do
    bdyb <- rslvRoDiffs vs cvs vmap bdy
    return ([],bdyb)
rslvRoDiffsInLet vs cvs vmap ((CS.Binding ip m e bvs):bs) bdy = do
    eb <- rslvRoDiffs vs cvs vmap e
    let ipb = bangInPattern vs vmap esrcs ip
    ebm <- rslvRoDiffsInBinding vmap ipb eb
    ipbm <- cmpNotModified cvs ipb
{-
    bb <- if isRegular $ typOfGIP ip
             then return $ CS.Binding ip m eb bvs
             else do
                 iebs <- mapM (rslvRoDiffsInBinding vs cvs vmap) $ zip ips $ getExprList eb
                 let (ipsb,ebsb) = unzip iebs
                 return $ CS.Binding (mkIPatternFromList ipsb) m (mkExprFromList ebsb) bvs
                 -}
    let cvs' = union cvs $ getCvs vs vmap ip
        vmap' = addVarSourcesFromBinding vmap (ip, esrcs)
    (bsb,bdyb) <- rslvRoDiffsInLet vs cvs' vmap' bs bdy
    return ((CS.Binding ipbm m ebm bvs):bsb,bdyb)
    where esrcs = getExprSources vmap $ exprOfGE e
          {-
          ips = getIPatternsList ip
          mkIPatternFromList :: [GenIrrefPatn] -> GenIrrefPatn
          mkIPatternFromList [ip] = ip
          mkIPatternFromList ips = GenIrrefPatn (CS.PTuple ips) (orgOfGIP ip) (typOfGIP ip)
          mkExprFromList :: [GenExpr] -> GenExpr
          mkExprFromList [e] = e
          mkExprFromList es = GenExpr (CS.Tuple es) (orgOfGE e) (mkTupleType $ map typOfGE es) (ccdOfGE e)
          -}
          getCvs vs vmap (GenIrrefPatn (CS.PTuple ips) _ _) = nub $ concatMap (getCvs vs vmap) ips
          getCvs vs vmap (GenIrrefPatn (CS.PTake pv [Just (_,(GenIrrefPatn (CS.PVar cv) _ _))]) _ t)
              | not $ null $ intersect vs $ getVarSources vmap pv = [cv]
          getCvs vs vmap (GenIrrefPatn (CS.PArrayTake pv [(_,(GenIrrefPatn (CS.PVar cv) _ _))]) _ t)
              | not $ null $ intersect vs $ getVarSources vmap pv = [cv]
          getCvs _ _ _ = []

-- | Bang variable types in a pattern.
-- The first argument is a list of variables for which the type must be banged at every occurrence.
-- The second argument is the variable source map for all variables of linear type bound in the context.
-- The third argument is the list of source variables of the bound expression, according to the pattern seen as tuple.
-- Value variables and wildcards are banged according to the source variables of the bound expression.
-- Other variables are banged according to their own source variables.
-- In take patterns both variables are banged according to the source variables of the container.
bangInPattern :: [CCS.VarName] -> VarSourceMap -> [[CCS.VarName]] -> GenIrrefPatn -> GenIrrefPatn
bangInPattern vs vmap esrcs ip@(GenIrrefPatn (CS.PVar pv) o t) =
    if null $ intersect vs srcs
       then ip
       else GenIrrefPatn (CS.PVar pv) o $ mkReadonly t
    where srcs = if isValVar pv then head esrcs else getVarSources vmap pv
bangInPattern vs _ esrcs ip@(GenIrrefPatn CS.PUnderscore o t) =
    if null $ intersect vs $ head esrcs
       then ip
       else GenIrrefPatn CS.PUnderscore o $ mkReadonly t
bangInPattern vs vmap _ ip@(GenIrrefPatn (CS.PTake pv [Just (f,(GenIrrefPatn (CS.PVar cv) co ct))]) o t) =
    if null $ intersect vs $ getVarSources vmap pv
       then ip
       else GenIrrefPatn (CS.PTake pv [Just (f,(GenIrrefPatn (CS.PVar cv) co $ mkReadonly ct))]) o $ mkReadonly t
bangInPattern vs vmap _ ip@(GenIrrefPatn (CS.PArrayTake pv [(i,(GenIrrefPatn (CS.PVar cv) co ct))]) o t) =
    if null $ intersect vs $ getVarSources vmap pv
       then ip
       else GenIrrefPatn (CS.PArrayTake pv [(i,(GenIrrefPatn (CS.PVar cv) co $ mkReadonly ct))]) o $ mkReadonly t
bangInPattern vs vmap esrcs (GenIrrefPatn (CS.PTuple ips) o t) =
    GenIrrefPatn (CS.PTuple ipsb) o (mkTupleType (map typOfGIP ipsb))
    where ipsb = map (\(ip,esrc) -> bangInPattern vs vmap [esrc] ip) $ zip ips esrcs
bangInPattern _ _ _ ip = ip

-- | Resolve readonly type incompatibilities in a binding, given by a pattern and an expression.
-- The first argument is the variable source map for all variables of linear type bound in the context.
-- If the pattern is readonly, the expression is linear, and it has source variables: register the source variables for banging.
-- Otherwise replace the expression by a dummy with a type compatible to the pattern type and record an error.
rslvRoDiffsInBinding :: VarSourceMap -> GenIrrefPatn -> GenExpr -> Trav [CCS.VarName] GenExpr
rslvRoDiffsInBinding vmap ip@(GenIrrefPatn (CS.PTuple _) _ _) (GenExpr (CS.Let bs bdy) o t s) = do
    bdyb <- rslvRoDiffsInBinding (addVarSourcesFromBindings vmap bs) ip bdy
    return $ GenExpr (CS.Let bs bdyb) o (typOfGE bdyb) s
rslvRoDiffsInBinding vmap ip@(GenIrrefPatn (CS.PTuple _) _ _) (GenExpr (CS.If e0 bvs e1 e2) o t s) = do
    e1b <- rslvRoDiffsInBinding vmap ip e1
    e2b <- rslvRoDiffsInBinding vmap ip e2
    return $ GenExpr (CS.If e0 bvs e1b e2b) o (typOfGE e1b) s
rslvRoDiffsInBinding vmap (GenIrrefPatn (CS.PTuple ips) _ _) (GenExpr (CS.Tuple es) o t s) = do
    esb <- mapM (\(ip,e) -> rslvRoDiffsInBinding vmap ip e) $ zip ips es
    return $ GenExpr (CS.Tuple esb) o (mkTupleType (map typOfGE esb)) s
rslvRoDiffsInBinding vmap (GenIrrefPatn _ _ pt) e = matchRoExpr vmap pt e

-- | Check whether a variable is modified by a pattern.
-- The first argument is a list of variables which may not be modified.
-- If it occurs in the pattern it is replaced by the error variable and an error is recorded.
cmpNotModified :: [CCS.VarName] -> GenIrrefPatn -> Trav [CCS.VarName] GenIrrefPatn
cmpNotModified cvs ip@(GenIrrefPatn (CS.PVar pv) o t) | elem pv cvs = do
    recordError $ typeMatch o "Component of readonly struct modified"
    return $ GenIrrefPatn (CS.PVar errVar) o t
cmpNotModified cvs (GenIrrefPatn (CS.PTuple ips) o t) = do
    ipsm <- mapM (cmpNotModified cvs) ips
    return $ GenIrrefPatn (CS.PTuple ipsm) o t
cmpNotModified _ ip = return ip



-- | Bang variable types and resolve readonly type incompatibilities in a binding given by a pattern and the bound expression.
{-}
rslvRoDiffsInBinding :: [CCS.VarName] -> [CCS.VarName] -> VarSourceMap -> (GenIrrefPatn,GenExpr)
    -> Trav [CCS.VarName] (GenIrrefPatn,GenExpr)
rslvRoDiffsInBinding vs cvs vmap (ip@(GenIrrefPatn (CS.PTuple _) _ _), (GenExpr (CS.Let bs bdy) o t s)) = do
    (ipb,bdyb) <- rslvRoDiffsInBinding vs cvs (addVarSourcesFromBindings bs) (ip,bdy)
    return (ipb, GenExpr (CS.Let bs bdyb) o (typOfGE bdyb) s)
rslvRoDiffsInBinding vs cvs vmap (ip@(GenIrrefPatn (CS.PTuple _) _ _), (GenExpr (CS.If e0 bvs e1 e2) o t s)) = do

rslvRoDiffsInBinding vs cvs vmap (ip@(GenIrrefPatn (CS.PVar pv) o t), e) | isValVar pv =
    if not $ null $ intersect vs $ head $ getExprSources vmap $ exprOfGE e
       then return (GenIrrefPatn (CS.PVar pv) o $ mkReadonly t, e)
       else return (ip,e)
rslvRoDiffsInBinding vs cvs vmap (ip@(GenIrrefPatn (CS.PVar pv) o t), e) =
    if elem pv cvs
       then do
           recordError $ typeMatch o "Component of readonly struct modified"
           e' <- matchRoExpr vmap t' e
           return (GenIrrefPatn (CS.PVar errVar) o t', e')
       else if isRegular t
       then return (ip,e)
       else do
           e' <- matchRoExpr vmap t' e
           return (GenIrrefPatn (CS.PVar pv) o t', e')
    where t' = if null $ intersect vs $ getVarSources vmap pv then t else mkReadonly t
rslvRoDiffsInBinding vs cvs vmap (ip@(GenIrrefPatn CS.PUnderscore o t), e) =
    return (GenIrrefPatn CS.PUnderscore o (typOfGE e), e)
rslvRoDiffsInBinding vs cvs vmap (ip@(GenIrrefPatn (CS.PTake pv [Just (f,(GenIrrefPatn (CS.PVar cv) co ct))]) o t), e) =
    if null $ intersect vs $ getVarSources vmap pv
       then return (ip,e)
       else return (GenIrrefPatn (CS.PTake pv [Just (f,(GenIrrefPatn (CS.PVar cv) co (mkReadonly ct)))]) o $ mkReadonly t, e)
rslvRoDiffsInBinding vs cvs vmap (ip@(GenIrrefPatn (CS.PArrayTake pv [(i,(GenIrrefPatn (CS.PVar cv) co ct))]) o t), e) =
    if null $ intersect vs $ getVarSources vmap pv
       then return (ip,e)
       else return (GenIrrefPatn (CS.PArrayTake pv [(i,(GenIrrefPatn (CS.PVar cv) co (mkReadonly ct)))]) o $ mkReadonly t, e)
-}

-- | Resolve readonly type incompatibilities between a type and an expression.
-- If the type must be banged the result is a dummy expression of the type and an error is recorded.
-- Otherwise, if the expression must be banged its source variables are added to the state and the expression is returned.
-- If the expression has no source variables the result is a dummy expression of the type and an error is recorded.
matchRoExpr :: VarSourceMap -> GenType -> GenExpr -> Trav [CCS.VarName] GenExpr
matchRoExpr vmap (GenType (CS.TTuple ts) _ _) (GenExpr (CS.Tuple es) o t s) = do
    esb <- mapM (uncurry (matchRoExpr vmap)) $ zip ts es
    return $ GenExpr (CS.Tuple esb) o (mkTupleType (map typOfGE esb)) s
matchRoExpr vmap t e =
    if tb
       then do
           recordError $ typeMatch (orgOfGE e) msg
           return $ toDummyExpr e $ mkDummyExpr t msg
       else if eb
       then tryBang vmap e
       else return e
    where (tb,eb) = matchRoTypes t $ typOfGE e
          msg = "Readonly expression used in linear context"

-- | Try to bang an expression.
-- If it is no variable or has no source variables the result is a dummy expression of the banged type and an error is recorded.
-- Otherwise its source variables are added to the state and the expression is returned.
tryBang :: VarSourceMap -> GenExpr -> Trav [CCS.VarName] GenExpr
tryBang vmap e =
    case exprOfGE e of
         CS.Var v -> if null $ getVarSources vmap v
                        then do
                            recordError $ typeMatch (orgOfGE e) msg
                            return $ toDummyExpr e $ mkDummyExpr t msg
                        else do
                            recordSources vmap v
                            return e
         _ -> do
             recordError $ typeMatch (orgOfGE e) msg
             return $ toDummyExpr e $ mkDummyExpr t msg
    where t = mkReadonly $ typOfGE e
          msg = "Linear expression used in readonly context"

-- | Resolve readonly type incompatibilities between two expressions.
-- For the expression(s) to be banged, the source variables are added to the state and the expression is returned.
-- If an expression to be banged has no source variables the result is a dummy expression of the type and an error is recorded.
-- If at least one expression must be banged, the returned type is the banged type of the first expression,
-- otherwise it is the type of the first expression.
matchRoExprs :: VarSourceMap -> GenExpr -> GenExpr -> Trav [CCS.VarName] (GenExpr,GenExpr,GenType)
matchRoExprs vmap e1 e2 =
    if eb1 && eb2
       then do
           e1b <- tryBang vmap e1
           e2b <- tryBang vmap e2
           return (e1b,e2b,mkReadonly $ typOfGE e1)
       else if eb1
       then do
           e1b <- tryBang vmap e1
           return (e1b,e2,typOfGE e2)
       else if eb2
       then do
           e2b <- tryBang vmap e2
           return (e1,e2b,typOfGE e1)
       else return (e1,e2,typOfGE e1)
    where (eb1,eb2) = matchRoTypes (typOfGE e1) (typOfGE e2)

-- | Resolve readonly type incompatibilities between two types.
-- The result is True for the type(s) which must be banged so that both are readonly compatible.
-- Assumes that the types differ atmost by MayNull and read-only
-- or one is String and the other is array of U8.
matchRoTypes :: GenType -> GenType -> (Bool,Bool)
matchRoTypes t1 t2 | roCmpTypes t1 t2 = (False,False)
matchRoTypes t1 t2 =
    if roCmpTypes (mkReadonly t1) t2
       then (True,False)
       else if roCmpTypes t1 (mkReadonly t2)
       then (False,True)
       else (True,True)


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
