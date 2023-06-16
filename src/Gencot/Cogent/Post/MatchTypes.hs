{-# LANGUAGE PackageImports #-}
module Gencot.Cogent.Post.MatchTypes where

import Data.List (intercalate,concatMap,nub,intersect,union,(\\),partition,find,zipWith,zip3, zip4)
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
{- For readonly subexpressions in -}
{- linear context: record error   -}
{----------------------------------}

bangproc :: GenExpr -> ETrav GenExpr
bangproc e = mapMExprOfGE bangproc' e

-- | Try to bang variables in subexpressions where that is possible.
-- Banging is possible in conditions of conditional expressions and in bindings.
-- No bang tried in CS.Match, CS.LamC, CS.MultiWayIf, because these are not generated.
bangproc' :: ExprOfGE -> ETrav ExprOfGE
bangproc' (CS.Let bs bdy) = do
    bsb <- bangprocInLet bs $ exprOfGE bdy
    bdyp <- bangproc bdy
    return $ CS.Let bsb bdyp
bangproc' (CS.If e [] e1 e2) = do
    (eb,bvs,errs) <- runExprTrav [] $ bangprocExpr e
    -- type of eb is always escapeable because it is boolean
    mapM recordError errs
    (ebe,bvse) <- if null errs then extendBangExpr eb bvs else return (eb,bvs)
    e1p <- bangproc e1
    e2p <- bangproc e2
    return $ CS.If ebe bvse e1p e2p
bangproc' e = mapM bangproc e

-- | Try to bang variables in the bindings of a let expressions.
-- The let body is required to determine the variables used in it, it is not processed.
-- Bindings are processed in their order in the let expression.
bangprocInLet :: [GenBnd] -> ExprOfGE -> ETrav [GenBnd]
bangprocInLet [] _ = return []
bangprocInLet bs bdy = do
    (bb : bsr) <- bangprocInBindings bs bdy
    bsrp <- bangprocInLet bsr bdy
    return (bb : bsrp)

-- | Try to bang variables in a prefix of a binding sequence.
-- The shortest prefix is used for which the result is escapeable.
-- If successful, the prefix is converted to a single binding with banged variables.
-- This binding binds (only) the variables which occur free in the remaining bindings followed by the expression.
-- Otherwise the sequence is returned unmodified.
bangprocInBindings :: [GenBnd] -> ExprOfGE -> ETrav [GenBnd]
bangprocInBindings [] _ = return []
bangprocInBindings (b@(CS.Binding ip m e []):bs) bdy = do
    (eb,bvs,errs) <- runExprTrav [] $ bangprocExpr e
    let (ipr,ebr) = reduceBangedBinding bvs ip eb
    if null bvs || (mayEscape $ typOfGE ebr)
       then do
           mapM recordError errs
           (ebre,bvse) <- if null errs then extendBangExpr ebr bvs else return (ebr,bvs)
           bsb <- bangprocInBindings bs bdy
           let (ibs,ebs) = matchRoTypes (typOfGIP ipr) (typOfGE ebre)
               msgp = if null bvse then "" else "After banging variable(s)"
           ebreb <- markLinearAsError msgp ebs ebre
           (ebrebb,_,errs2) <- runExprTrav [] $ markReadonlyAsError ibs (typOfGIP ipr) ebreb
           mapM recordError errs2
           return ((CS.Binding ipr m ebrebb bvse) : bsb)
       else if null bs
       then do
           mapM recordError errs
           let msg = "Necessary banging of variables " ++ (intercalate ", " bvs) ++ " leads to non-escapeable type"
           recordError $ typeMatch (orgOfGIP ip) msg
           if roCmpTypes (typOfGIP ipr) (typOfGE ebr)
              then return $ [CS.Binding ipr m (bangToError bvs ebr) bvs]
              else return $ [CS.Binding ipr m (toDummyExpr ebr $ mkDummyExpr (typOfGIP ipr) msg) []]
       else bangprocInBindings (combineBindings b (head bs) (tail bs) bdy) bdy

-- | Reduce a binding by removing components which are obsolete after banging variables.
-- Such components are bindings of a banged variable to itself or a put expression for itself.
-- If the variable is banged in the binding it cannot be modified in the bound expression, hence it needs no re-binding.
-- It is crucial to remove such components, otherwise the type of the bound expression becomes unescapeable
-- which would prevent the banging.
reduceBangedBinding :: [CCS.VarName] -> GenIrrefPatn -> GenExpr -> (GenIrrefPatn, GenExpr)
reduceBangedBinding [] ip e = (ip,e)
reduceBangedBinding bvs ip@(GenIrrefPatn (CS.PTuple ips) op tp) (GenExpr (CS.Let bs bdy) oe te ce) =
    (ip', GenExpr (CS.Let bs bdy') oe (typOfGE bdy') ce)
    where (ip',bdy') = reduceBangedBinding bvs ip bdy
-- Not sure how to handle this case and whether it is necessary to be handled at all:
reduceBangedBinding bvs ip@(GenIrrefPatn (CS.PTuple ips) op tp) e@(GenExpr (CS.If e0 _ e1 e2) oe te ce) = (ip,e)
reduceBangedBinding bvs (GenIrrefPatn (CS.PTuple ips) op tp) (GenExpr (CS.Tuple es) oe te ce) =
    let (ips',es') = unzip $ filter retain $ zip ips es
    in (GenIrrefPatn (CS.PTuple ips') op (mkTupleType $ map typOfGIP ips'), GenExpr (CS.Tuple es') oe (mkTupleType $ map typOfGE es') ce)
    where retain (GenIrrefPatn (CS.PVar pv) _ _, GenExpr (CS.Var v) _ _ _)
            | pv == v && elem v bvs = False
          retain (GenIrrefPatn (CS.PVar pv) _ _, GenExpr (CS.Put (GenExpr (CS.Var v) _ _ _) _) _ _ _)
            | pv == v && elem v bvs = False
          retain (GenIrrefPatn (CS.PVar pv) _ _, GenExpr (CS.ArrayPut (GenExpr (CS.Var v) _ _ _) _) _ _ _)
            | pv == v && elem v bvs = False
          retain _ = True
reduceBangedBinding _ ip e = (ip,e)

-- | Replace some subexpressions of linear type by dummy expressions.
-- The first argument is a string to be prepended to the error messages.
-- The second argument is a boolean vector specifying the tuple components to be replaced,
-- if the expression is seen as a tuple.
markLinearAsError :: String -> [Bool] -> GenExpr -> ETrav GenExpr
markLinearAsError _ bools e | not $ or bools = return e
markLinearAsError msgp [True] e = do
    recordError $ typeMatch (orgOfGE e) msg
    return $ toDummyExpr e $ mkDummyExpr t msg
    where t = mkReadonly $ typOfGE e
          msgr = "inear expression used in readonly context"
          msg = if null msgp
                   then "L" ++ msgr
                   else msgp ++ " l" ++ msgr
markLinearAsError msgp bools (GenExpr (CS.Tuple es) o t s) = do
    esb <- mapM (\(b,e) -> markLinearAsError msgp [b] e) $ zip bools es
    return $ GenExpr (CS.Tuple esb) o (mkTupleType (map typOfGE esb)) s
markLinearAsError msgp bools (GenExpr (CS.Let bs bdy) o t s) = do
    bdyb <- markLinearAsError msgp bools bdy
    return $ GenExpr (CS.Let bs bdyb) o (typOfGE bdyb) s
markLinearAsError msgp bools e@(GenExpr (CS.App _ _ _) _ _ _) = do
    recordError $ typeMatch (orgOfGE e) msg
    return $ toDummyExpr e $ mkDummyExpr (mkReadonly $ typOfGE e) msg
    where poss = (show $ map snd $ filter fst $ zip bools (iterate (1 +) 1))
          msgr = "inear function result used in readonly context at position(s): " ++ poss
          msg = if null msgp
                   then "L" ++ msgr
                   else msgp ++ " l" ++ msgr
markLinearAsError msgp bools (GenExpr (CS.If e0 bvs e1 e2) o t s) = do
    e1b <- markLinearAsError msgp bools e1
    e2b <- markLinearAsError msgp bools e2
    return $ GenExpr (CS.If e0 bvs e1b e2b) o (typOfGE e1b) s

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

-- | Try to find variables which can be banged to resolve readonly type incompatibilities in an expression.
-- If it is not possible to resolve all readonly type incompatibilities in this way,
-- and the expression contains bang positions, it is instead processed by bangproc to try the inner bang positions.
-- Otherwise in the monadic state a minimal set of variables is returned which must be banged.
-- Remaining incompatibiliteis are resolved using dummy expressions, returning corresponding error messages in the monadic state.
-- In the returned expressions all readonly type incompatibilities have been resolved.
bangprocExpr :: GenExpr -> Trav [CCS.VarName] GenExpr
bangprocExpr e = do
    (eb,bvs,errs) <- runExprTrav [] $ tryBangExpr e
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

-- | Resolve readonly type incompatibilities in an expression by banging variables.
-- The result is the expression with resolved incompatibilities.
-- Additionally the monadic state contains the set of variable names which must be banged
-- to change the expression accordingly.
-- If there are readonly type incompatibilities which cannot be resolved by banging variables
-- they are resolved by using dummy expressions and recording corresponding errors.
tryBangExpr :: GenExpr -> Trav [CCS.VarName] GenExpr
tryBangExpr e = bangVars [] e

-- | Try to bang additional variables in an expression.
-- Candidates are all free variables which occur as container with linear type in a take operation.
-- The result is the expression with additional types banged and the extended set of variables to bang.
extendBangExpr :: GenExpr -> [CCS.VarName] -> ETrav (GenExpr, [CCS.VarName])
extendBangExpr e vs = do
    (eb,bvs) <- extendBangVars e $ getBangCandidates [] e
    return (eb,union vs bvs)

-- | Try to change variable types to readonly in an expression according to a list of typed variables.
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

-- | Change the types to readonly at every occurrence of variables in the given list.
-- Resulting readonly type incompatibilities for other variables are resolved
-- by changing their types at every occurrence as well.
-- All other incompatibilities are resolved by replacing expressions by dummy expressions with errors recorded.
-- The result is the changed expression where all readonly type incompatibilities have been resolved.
-- In the monadic state the set of all variables is returned for which the type has been changed.
bangVars :: [CCS.VarName] -> GenExpr -> Trav [CCS.VarName] GenExpr
bangVars vs e = do
    modifyUserState (\s -> union vs s)
    (eb,bvs,errs) <- runExprTrav [] $ rslvRoDiffs vs [] M.empty e
    mapM recordError errs
    if null bvs
       then return eb
       else bangVars bvs eb

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
    ebm <- matchRoExpr vmap (typOfGIP ipb) eb
    ipbm <- cmpNotModified cvs ipb
    let cvs' = union cvs $ getCvs vs vmap ip
        vmap' = addVarSourcesFromBinding vmap (ip, esrcs)
    (bsb,bdyb) <- rslvRoDiffsInLet vs cvs' vmap' bs bdy
    return ((CS.Binding ipbm m ebm bvs):bsb,bdyb)
    where esrcs = getExprSources vmap $ exprOfGE e
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

-- | Resolve readonly type incompatibilities between a type and an expression.
-- If the type must be banged the result is a dummy expression of the type and an error is recorded.
-- Otherwise, if the expression must be banged its source variables are added to the state and the expression is returned.
-- If the expression has no source variables the result is a dummy expression of the type and an error is recorded.
-- If the type is a tuple type the expression must also have a tuple type of the same size,
-- then the type incompatibilities are resolved between the corresponding tuple components.
matchRoExpr :: VarSourceMap -> GenType -> GenExpr -> Trav [CCS.VarName] GenExpr
matchRoExpr vmap t e = do
    eb <- changeLinToRoInExpr vmap ebs e
    markReadonlyAsError tbs t eb
    where (tbs,ebs) = matchRoTypes t $ typOfGE e

-- | Resolve readonly type incompatibilities between two expressions.
-- For the expression(s) to be banged, the source variables are added to the state and the expression is returned.
-- If an expression to be banged has no source variables the result is a dummy expression of the type and an error is recorded.
-- If at least one expression must be banged, the returned type is the banged type of the first expression,
-- otherwise it is the type of the first expression.
matchRoExprs :: VarSourceMap -> GenExpr -> GenExpr -> Trav [CCS.VarName] (GenExpr,GenExpr,GenType)
matchRoExprs vmap e1 e2 = do
    e1b <- changeLinToRoInExpr vmap eb1s e1
    e2b <- changeLinToRoInExpr vmap eb2s e2
    return (e1b,e2b,t)
    where t1 = (typOfGE e1)
          t2 = (typOfGE e2)
          (eb1s,eb2s) = matchRoTypes t1 t2
          t = changeLinToRoInTypes eb1s eb2s t1 t2

-- | Replace some subexpressions of readonly type by dummy expressions.
-- The first argument is a boolean vector specifying the tuple components to be replaced,
-- if the expression is seen as a tuple.
-- The second argument is the type which the expression shall have after the replacements.
markReadonlyAsError :: [Bool] -> GenType -> GenExpr -> Trav [CCS.VarName] GenExpr
markReadonlyAsError bools _ e | not $ or bools = return e
markReadonlyAsError [True] t e = do
    recordError $ typeMatch (orgOfGE e) msg
    return $ toDummyExpr e $ mkDummyExpr t msg
    where msg = "Readonly expression used in linear context"
markReadonlyAsError bools (GenType (CS.TTuple ts) _ _) (GenExpr (CS.Tuple es) o _ s) = do
    esb <- mapM (\(b,t,e) -> markReadonlyAsError [b] t e) $ zip3 bools ts es
    return $ GenExpr (CS.Tuple esb) o (mkTupleType (map typOfGE esb)) s
markReadonlyAsError bools t (GenExpr (CS.Let bs bdy) o _ s) = do
    bdyb <- markReadonlyAsError bools t bdy
    return $ GenExpr (CS.Let bs bdyb) o (typOfGE bdyb) s
markReadonlyAsError bools t e@(GenExpr (CS.App _ _ _) _ _ _) = do
    recordError $ typeMatch (orgOfGE e) msg
    return $ toDummyExpr e $ mkDummyExpr t msg
    where poss = (show $ map snd $ filter fst $ zip bools (iterate (1 +) 1))
          msg = ("Readonly function result used in linear context at position(s): " ++ poss)
markReadonlyAsError bools t (GenExpr (CS.If e0 bvs e1 e2) o _ s) = do
    e1b <- markReadonlyAsError bools t e1
    e2b <- markReadonlyAsError bools t e2
    return $ GenExpr (CS.If e0 bvs e1b e2b) o (typOfGE e1b) s

-- | Change some subexpressions of linear type to readonly type.
-- The second argument is a boolean vector specifying the tuple components to be changed,
-- if the expression is seen as a tuple.
-- If a component is no variable or has no source variables it is replaced by a dummy expression of the readonly type and an error is recorded.
-- Otherwise its source variables are added to the state and the expression is returned.
changeLinToRoInExpr :: VarSourceMap -> [Bool] -> GenExpr -> Trav [CCS.VarName] GenExpr
changeLinToRoInExpr _ bools e | not $ or bools = return e
changeLinToRoInExpr vmap [True] e =
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
changeLinToRoInExpr vmap bools (GenExpr (CS.Tuple es) o t s) = do
    esb <- mapM (\(b,e) -> changeLinToRoInExpr vmap [b] e) $ zip bools es
    return $ GenExpr (CS.Tuple esb) o (mkTupleType (map typOfGE esb)) s
changeLinToRoInExpr vmap bools (GenExpr (CS.Let bs bdy) o t s) = do
    bdyb <- changeLinToRoInExpr (addVarSourcesFromBindings vmap bs) bools bdy
    return $ GenExpr (CS.Let bs bdyb) o (typOfGE bdyb) s
changeLinToRoInExpr _ bools e@(GenExpr (CS.App _ _ _) _ _ _) = do
    recordError $ typeMatch (orgOfGE e) msg
    return $ toDummyExpr e $ mkDummyExpr (mkReadonly $ typOfGE e) msg
    where poss = (show $ map snd $ filter fst $ zip bools (iterate (1 +) 1))
          msg = ("Linear function result used in readonly context at position(s): " ++ poss)
changeLinToRoInExpr vmap bools (GenExpr (CS.If e0 bvs e1 e2) o t s) = do
    e1b <- changeLinToRoInExpr vmap bools e1
    e2b <- changeLinToRoInExpr vmap bools e2
    return $ GenExpr (CS.If e0 bvs e1b e2b) o (typOfGE e1b) s

-- | Change some linear type components to readonly to resolve incompatibilities between two types.
-- The first and second arguments are boolean vectors specifying the type components to be changed,
-- if the types are seen as tuple types.
-- The result consists of all changed components and the remaining components from the first type.
changeLinToRoInTypes :: [Bool] -> [Bool] -> GenType -> GenType -> GenType
changeLinToRoInTypes [b1] [b2] t1 t2 =
    if b1 then mkReadonly t1
          else if b2 then mkReadonly t2
                     else t1
changeLinToRoInTypes bs1 bs2 (GenType (CS.TTuple ts1) o _) (GenType (CS.TTuple ts2) _ _) =
    GenType (CS.TTuple ts) o Nothing
    where ts = map (\(b1,b2,t1,t2) -> changeLinToRoInTypes [b1] [b2] t1 t2) $ zip4 bs1 bs2 ts1 ts2

-- | Resolve readonly type incompatibilities between two types.
-- Types are seen as tuples, the results are two boolean lists according to the tuple components.
-- The result is True for a component which must be banged so that it is readonly compatible with the corresponding component.
-- Assumes that the type components differ atmost by MayNull and read-only or one is String and the other is array of U8.
matchRoTypes :: GenType -> GenType -> ([Bool],[Bool])
matchRoTypes (GenType (CS.TTuple ts1) _ _) (GenType (CS.TTuple ts2) _ _) =
    unzip $ map (uncurry matchRoTypes') $ zip ts1 ts2
matchRoTypes t1 t2 = unzip [matchRoTypes' t1 t2]

matchRoTypes' :: GenType -> GenType -> (Bool,Bool)
matchRoTypes' t1 t2 | roCmpTypes t1 t2 = (False,False)
matchRoTypes' t1 t2 =
    if roCmpTypes (mkReadonly t1) t2
       then (True,False)
       else if roCmpTypes t1 (mkReadonly t2)
       then (False,True)
       else (True,True)
