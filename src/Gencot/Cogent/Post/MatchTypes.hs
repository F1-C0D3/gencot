{-# LANGUAGE PackageImports #-}
module Gencot.Cogent.Post.MatchTypes where

import Control.Monad (liftM)
import Data.Char (isDigit)
import Data.List (intercalate,transpose,concatMap,foldl1',isPrefixOf,nub,intersect,union,(\\),partition,find,zipWith,zip3, zip4)
import qualified Data.Map as M
import Data.Maybe (catMaybes,isNothing,isJust,fromJust)
import Data.Foldable (toList)

import Language.C.Data.Error
import Language.C.Analysis as LCA (Trav,recordError,getUserState,modifyUserState)

import Cogent.Surface as CS
import Cogent.Common.Syntax as CCS

import Gencot.Names (mapNull)
import Gencot.Cogent.Ast
import Gencot.Cogent.Error (typeMatch)
import Gencot.Cogent.Types (
  mkBoolType, mkU8Type, mkU16Type, mkU32Type, mkU64Type, mkTupleType, mkFunType, mkReadonly, mkOption, mkMayNull,
  isBoolType, isTupleType, isNonlinear, isRegular, mayEscape, isReadonly, isMayNull, isArithmetic, roCmpTypes,
  unbangType, getMemberType, getDerefType, getNnlType, getParamType, getResultType, adaptTypes)
import Gencot.Cogent.Bindings (errVar, isValVarName, mkDummyExpr, toDummyExpr, mkVarBinding, mkVarPattern, mkVarTuplePattern)
import Gencot.Cogent.Expr (
  TypedVar(TV), namOfTV, typOfTV, mkUnitExpr, mkIntLitExpr, mkNullExpr, mkVarExpr, mkOpExpr, mkBoolOpExpr, mkUpcastExpr,
  mkTopLevelFunExpr, mkAppExpr, mkLetExpr, mkIfExpr, mkMatchExpr, mkTupleExpr, mkVarTupleExpr)
import Gencot.Cogent.Post.Util (
  ETrav, runExprTrav, isValVar, isCVar, freeInExpr, freeInExpr', freeInIrrefPatn, freeInBindings, freeUnderBinding, boundInBindings,
  returnedByExpr, modifiedByBinding, exchangeableWithBindings,
  freeTypedVarsInExpr, freeTypedVarsUnderBinding,
  getIPatternsList, getExprList, isPutExpr)

-- Assumption for all expressions:
-- - expressions bound in a binding are only
--   literals, variables, tuples, constant or function names, function applications, operator applications,
--   put/array-put, conditional expressions, let-expressions
-- - the argument of a function application is a single variable or a tuple of variables.
-- - the body of a let-expresson is a single variable or a tuple of variables or a conditional expression.
-- - a branch in a conditional expressions is a single variable or a tuple of variables or a let-expression.
-- - all other sub-expressions are single variables.
-- Assumptions for all patterns:
-- - irrefutable patterns in a binding are only
--   variables, tuples, wildcard, take, or array-take
-- - subpatterns in tuples are only variables or wildcards, or the tuple is a pair of an array-take and a variable.
--   array-takes only occur in such pairs.
-- - a take or array-take has exactly one taken field or element

{- Matching Boolean Types with  -}
{- Arithmetic and Pointer Types -}
{--------------------------------}

boolproc :: GenExpr -> ETrav GenExpr
boolproc = resolveExpr convVarBoolDiffs

convVarBoolDiffs :: ConvVarFun
convVarBoolDiffs e t | typOfGE e == t = return Nothing
convVarBoolDiffs e@(GenExpr (CS.Var v) o t1 _) t2 | isBoolType t1 && isArithmetic t2 =
    return $ Just $ mkVarBinding (TV v t2)
         $ mkIfExpr mkU32Type e (mkIntLitExpr mkU32Type 1) (mkIntLitExpr mkU32Type 0)
convVarBoolDiffs e@(GenExpr (CS.Var v) o t1 _) t2 | isArithmetic t1 && isBoolType t2 =
    return $ Just $ mkVarBinding (TV v t2) $ mkBoolOpExpr "/=" [e,mkIntLitExpr (typOfGE e) 0]
convVarBoolDiffs e@(GenExpr (CS.Var v) o t1 _) t2 | isBoolType t2 =
    return $ Just $ mkVarBinding (TV v t2) $ mkBoolOpExpr "/=" [e,mkNullExpr]
convVarBoolDiffs _ _ = return Nothing

{- Matching Arithmetic Types -}
{- with Each Other           -}
{-----------------------------}

intproc :: GenExpr -> ETrav GenExpr
intproc = resolveExpr convVarIntDiffs

convVarIntDiffs :: ConvVarFun
convVarIntDiffs e t | not ((isArithmetic $ typOfGE e) && isArithmetic t) = return Nothing
convVarIntDiffs e@(GenExpr (CS.Var v) o t1 _) t2 = do
    let cnve = if s1 < s2
               then mkUpcastExpr t2 e
               else if (s1 < 64) || (s2 > 8)
               then mkAppExpr (conv s1 s2) e
               else -- no direct conversion from U64 to U8 provided by Cogent, using two steps
                    mkLetExpr [mkVarBinding (TV v mkU32Type) $ mkAppExpr (conv 64 32) e,
                               mkVarBinding (TV v t2) $ mkAppExpr (conv 32 s2) $ mkVarExpr (TV v mkU32Type)]
                              $ mkVarExpr (TV v t2)
    if s1 == s2 then return Nothing
                else return $ Just $ mkVarBinding (TV v t2) cnve
    where s1 = getIntSize t1
          s2 = getIntSize t2
          conv 64 32 = mkVarExpr $ TV "u64_to_u32" $ mkFunType mkU64Type mkU32Type
          conv 64 16 = mkVarExpr $ TV "u64_to_u16" $ mkFunType mkU64Type mkU16Type
          conv 32 16 = mkVarExpr $ TV "u32_to_u16" $ mkFunType mkU32Type mkU16Type
          conv 32 8  = mkVarExpr $ TV "u32_to_u8"  $ mkFunType mkU32Type mkU8Type
          conv 16 8  = mkVarExpr $ TV "u16_to_u8"  $ mkFunType mkU16Type mkU8Type

getIntSize :: GenType -> Int
getIntSize (GenType (CS.TCon tn [] _) _ _) =
    case tn of
         "U8" -> 8
         "U16" -> 16
         "U32" -> 32
         "U64" -> 64
         _ -> 0

{- Matching linear subexpressions -}
{- to readonly context: try bang  -}
{- For readonly subexpressions in -}
{- linear context: record error   -}
{----------------------------------}

bangproc :: GenExpr -> ETrav GenExpr
bangproc e = do
    (eN,_,_) <- runExprTrav 0 $ mkNullUnique e
    eN' <- bangprocN eN
    reNullUnique eN'

mkNullUnique :: GenExpr -> Trav Int GenExpr
mkNullUnique e = mapMExprOfGE mkNullUnique' e

mkNullUnique' :: ExprOfGE -> Trav Int ExprOfGE
mkNullUnique' (CS.Var v) | v == mapNull = do
    n <- getUserState
    modifyUserState (\n -> n+1)
    return (CS.Var $ uniqueNull n)
mkNullUnique' e = mapM mkNullUnique e

uniqueNull :: Int -> String
uniqueNull n = "cogent" ++ (show n) ++ "_NULL"

isUniqueNull :: String -> Bool
isUniqueNull s = "cogent" `isPrefixOf` s && (dropWhile isDigit $ drop 6 s) == "_NULL"

reNullUnique :: GenExpr -> ETrav GenExpr
reNullUnique e = mapMExprOfGE reNullUnique' e

reNullUnique' :: ExprOfGE -> ETrav ExprOfGE
reNullUnique' (CS.Var v) | isUniqueNull v = return (CS.Var mapNull)
reNullUnique' e = mapM reNullUnique e

bangprocN :: GenExpr -> ETrav GenExpr
bangprocN e = mapMExprOfGE bangproc' e

-- | Resolve readonly type incompatibilities by banging variables or using dummy expressions with error messages.
-- Banging is possible in conditions of conditional expressions and in bindings.
-- No bang tried in CS.Match, because generated match expressions for NULL test would never be escapeable when banged.
-- No bang tried in CS.LamC, CS.MultiWayIf, because these are not generated.
-- Since variables are only banged in sub-contexts, and the effects may not escape these sub-contexts,
-- the type of the expression remains unchanged.
bangproc' :: ExprOfGE -> ETrav ExprOfGE
bangproc' (CS.Let bs bdy) = do
    bsb <- bangprocInBindings bs [] $ freeTypedVarsInExpr bdy
    bdyp <- bangprocN bdy
    return $ CS.Let bsb bdyp
bangproc' (CS.If e [] e1 e2) = do
    (eb,bvs,errs) <- runExprTrav [] $ bangprocExpr e
    -- type of eb is always escapeable because it is boolean
    mapM recordError errs
    e1p <- bangprocN e1
    e2p <- bangprocN e2
    return $ CS.If eb bvs e1p e2p
bangproc' e = mapM bangprocN e

-- | Resolve readonly type incompatibilities in a binding sequence by banging sub-sequences.
-- For banging variables, maximal sub-sequences are banged for which the type of the results used in the rest of the sequence is escapeable.
-- Such sub-sequences are converted to a single binding with banged variables.
-- The second argument is a part of the sequence for which the first part cannot be extended to a valid sub-sequence.
-- The third argument is the set of variables which are used after both parts of the sequence.
-- The result is a sequence which is equivalent to both parts and where all readonly type incompatibilities
-- have been resolved, either by banging variables or by using dummy expressions and error messages.
-- In case of error, the result sequence may contain banged scopes with non-escapeable type.
bangprocInBindings :: [GenBnd] -> [GenBnd] -> [TypedVar] -> ETrav [GenBnd]
bangprocInBindings [] [] _ = return []
bangprocInBindings [] _ _ = error "Empty binding sequence in bangprocInBindings" -- should not happen.
bangprocInBindings [CS.Binding ip m e []] br fvs = do
    (eb,bvs,errs) <- runExprTrav [] $ bangprocExpr e
    let (ipr,ebr) = reduceBangedBinding bvs ip eb
    if null bvs || (mayEscape $ typOfGE ebr)
       then do -- successfully resolved bound expression in single binding. Match to pattern and process br.
           mapM recordError errs
           brb <- bangprocInBindings br [] fvs
           let (ibs,ebs) = matchRoTypes (typOfGIP ipr) (typOfGE ebr)
               msgp = if null bvs then "" else "After banging variable(s)"
           ebreb <- markLinearAsError msgp (null bvs) ebs ebr
           (ebrebb,_,errs2) <- runExprTrav [] $ markReadonlyAsError ibs (typOfGIP ipr) ebreb
           mapM recordError errs2
           return ((CS.Binding ipr m ebrebb bvs) : brb)
       else do -- not successful for single binding. Record error and generate non-escapeable banging.
           mapM recordError errs
           brb <- bangprocInBindings br [] fvs
           let msg = "Necessary banging of variables " ++ (intercalate ", " bvs) ++ " leads to non-escapeable type"
           recordError $ typeMatch (orgOfGIP ip) msg
           if roCmpTypes (typOfGIP ipr) (typOfGE ebr)
              then return $ ((CS.Binding ipr m (bangToError bvs ebr) bvs) : brb)
              else return $ ((CS.Binding ipr m (toDummyExpr ebr $ mkDummyExpr (typOfGIP ipr) msg) []) : brb)
bangprocInBindings [CS.Binding _ _ _ bvs] _ _ = error "Binding already banged in bangprocInBindings" -- should not happen
bangprocInBindings bs br fvs = do
    (eb,bvs,errs) <- runExprTrav [] $ tryBangExpr e
    if null bvs -- no banging required. Use resolved bs and process br.
       then do
           let (GenExpr (CS.Let bsb _) _ _ _) = eb
           mapM recordError errs
           brb <- bangprocInBindings br [] fvs
           return (bsb ++ brb)
       else do
           let (ipr,ebr) = reduceBangedBinding bvs ip eb
           if (null errs && (mayEscape $ typOfGE ebr))
           then do -- successfully resolved in bs. Bang bvs in bs and process br.
               brb <- bangprocInBindings br [] fvs
               return ((CS.Binding ipr Nothing ebr bvs) : brb)
           else -- not successful for bs, try to bang sub-sequence
               bangprocInBindings (init bs) ((last bs) : br) $ freeTypedVarsUnderBinding [last bs] rvs
    where rvs = freeTypedVarsUnderBinding br fvs -- variables used after bs
          e = mkLetExpr bs $ mkVarTupleExpr $ rvs -- expression for representing bs as a single binding
          ip = mkVarTuplePattern rvs -- pattern for representing bs as a single binding

-- | Reduce a binding by replacing components which are obsolete after banging variables.
-- Obsolete components are replaced by unit bindings.
-- Obsolete components are bindings of a banged variable to itself or a put expression for itself.
-- If the variable is banged in the binding it cannot be modified in the bound expression, hence it needs no re-binding.
-- Bindings of a variable to a take pattern for itself as container are also obsolete, but must be retained for binding the component variable.
-- However, such bindings do no prevent to replace a component in the binding for the surrounding let expression.
-- It is crucial to replace obsolete components, otherwise the type of the bound expression becomes unescapeable
-- which would prevent the banging.
reduceBangedBinding :: [CCS.VarName] -> GenIrrefPatn -> GenExpr -> (GenIrrefPatn, GenExpr)
reduceBangedBinding bvs ip e = (ip',toUnitExprs ip' e')
    where (ip',e') = reduceBangedPatterns bvs ip e

-- | First pass: Only replace variable patterns by unit patterns
-- This makes it possible to restore the original pattern in case of alternatives where not all can be reduced.
-- The type of the expression remains unchanged.
reduceBangedPatterns :: [CCS.VarName] -> GenIrrefPatn -> GenExpr -> (GenIrrefPatn, GenExpr)
reduceBangedPatterns [] ip e = (ip,e)
reduceBangedPatterns bvs ip (GenExpr (CS.Let bs bdy) oe te ce) =
    (ip', GenExpr (CS.Let bs' bdy') oe te ce)
    where bs' = reduceBangedPatternsInBindings bvs bs
          bvs' = filter (unmodifiedInReducedBindings bs') bvs
          (ip',bdy') = reduceBangedPatterns bvs' ip bdy
reduceBangedPatterns bvs ip (GenExpr (CS.If e0 bvs0 e1 e2) oe te ce) =
    (mergeReducedPatterns [ip1', ip2'], GenExpr (CS.If e0 bvs0 e1' e2') oe te ce)
    where (ip1',e1') = reduceBangedPatterns bvs ip e1
          (ip2',e2') = reduceBangedPatterns bvs ip e2
reduceBangedPatterns bvs ip (GenExpr (CS.Match e0 bvs0 alts) oe te ce) =
    (mergeReducedPatterns ips, GenExpr (CS.Match e0 bvs0 alts') oe te ce)
    where (ips,es) = unzip $ map (\(CS.Alt p _ e) -> reduceBangedPatterns bvs ip e) alts
          alts' = map (\(CS.Alt p l _,e) -> CS.Alt p l e) $ zip alts es
-- if the expression is a tuple the pattern must also be a tuple
reduceBangedPatterns bvs (GenIrrefPatn (CS.PTuple ips) op tp) (GenExpr (CS.Tuple es) oe te ce) =
    (GenIrrefPatn (CS.PTuple ips') op (mkTupleType $ map typOfGIP ips'), GenExpr (CS.Tuple es') oe te ce)
    where (ips',es') = unzip $ map (uncurry $ reduceBangedPatterns bvs) $ zip ips es
reduceBangedPatterns bvs (GenIrrefPatn (CS.PVar pv) op tp) e@(GenExpr (CS.Var v) _ _ _)
    | pv == v && elem v bvs = (GenIrrefPatn CS.PUnitel op unitType,e)
reduceBangedPatterns bvs (GenIrrefPatn (CS.PVar pv) op tp) e@(GenExpr (CS.Put (GenExpr (CS.Var v) _ _ _) _) _ _ _)
    | pv == v && elem v bvs = (GenIrrefPatn CS.PUnitel op unitType,e)
reduceBangedPatterns bvs (GenIrrefPatn (CS.PVar pv) op tp) e@(GenExpr (CS.ArrayPut (GenExpr (CS.Var v) _ _ _) _) _ _ _)
    | pv == v && elem v bvs = (GenIrrefPatn CS.PUnitel op unitType,e)
reduceBangedPatterns _ ip e = (ip,e)

-- | Merge a list of reduced patterns.
-- The resulting pattern uses a unit pattern only if all input patterns do.
mergeReducedPatterns :: [GenIrrefPatn] -> GenIrrefPatn
mergeReducedPatterns ips@((GenIrrefPatn (CS.PTuple _) op _) : _) =
    GenIrrefPatn (CS.PTuple ips') op (mkTupleType $ map typOfGIP ips')
    where ips' = map mergeReducedPatterns $ transpose $ map (\(GenIrrefPatn (CS.PTuple ipss) _ _) -> ipss) ips
mergeReducedPatterns ips = case find (\ip -> irpatnOfGIP ip /= CS.PUnitel) ips of
                                Nothing -> head ips
                                Just ip -> ip

-- | Second pass: Replace bound expression by unit if corresponding pattern is unit.
toUnitExprs :: GenIrrefPatn -> GenExpr -> GenExpr
toUnitExprs ip (GenExpr (CS.Let bs bdy) oe te ce) =
    GenExpr (CS.Let bs' bdy') oe (toUnitTypes ip te) ce
    where bs' = toUnitExprsInBindings bs
          bdy' = toUnitExprs ip bdy
toUnitExprs ip (GenExpr (CS.If e0 bvs0 e1 e2) oe te ce) =
    GenExpr (CS.If e0 bvs0 e1' e2') oe (toUnitTypes ip te) ce
    where e1' = toUnitExprs ip e1
          e2' = toUnitExprs ip e2
toUnitExprs ip (GenExpr (CS.Match e0 bvs0 alts) oe te ce) =
    GenExpr (CS.Match e0 bvs0 alts') oe (toUnitTypes ip te) ce
    where alts' = map (\(CS.Alt p l e) -> CS.Alt p l $ toUnitExprs ip e) alts
toUnitExprs ip@(GenIrrefPatn (CS.PTuple ips) _ _) (GenExpr (CS.Tuple es) oe te ce) =
    GenExpr (CS.Tuple $ map (uncurry toUnitExprs) $ zip ips es) oe (toUnitTypes ip te) ce
toUnitExprs (GenIrrefPatn CS.PUnitel _ _) _ = mkUnitExpr
toUnitExprs _ e = e

toUnitExprsInBindings :: [GenBnd] -> [GenBnd]
toUnitExprsInBindings [] = []
toUnitExprsInBindings ((CS.Binding ip m e bvs) : bs) =
    (CS.Binding ip m e' bvs) : (toUnitExprsInBindings bs)
    where e' = toUnitExprs ip e

toUnitTypes :: GenIrrefPatn -> GenType -> GenType
toUnitTypes (GenIrrefPatn CS.PUnitel _ _) _ = unitType
toUnitTypes (GenIrrefPatn (CS.PTuple ips) _ _) (GenType (CS.TTuple ts) ot _) =
    mkTupleType $ map (uncurry toUnitTypes) $ zip ips ts
toUnitTypes _ t = t

-- | Reduce all bindings in a binding sequence.
reduceBangedPatternsInBindings :: [CCS.VarName] -> [GenBnd] -> [GenBnd]
reduceBangedPatternsInBindings bvs [] = []
reduceBangedPatternsInBindings bvs ((CS.Binding ip m e vs):bs) =
    (CS.Binding ip' m e' vs):bs'
    where (ip',e') = reduceBangedPatterns bvs ip e
          bs' = reduceBangedPatternsInBindings bvs bs

-- | Test whether a variable is modified in a binding sequence.
-- This is the case if it is atmost bound as container in a take binding.
-- We assume that take patterns are always bound to their own container variable.
unmodifiedInReducedBindings :: [GenBnd] -> CCS.VarName -> Bool
unmodifiedInReducedBindings [] _ = True
unmodifiedInReducedBindings ((CS.Binding ip _ _ _):bs) v =
    unmodifiedInReducedPattern v ip && unmodifiedInReducedBindings bs v

unmodifiedInReducedPattern :: CCS.VarName -> GenIrrefPatn -> Bool
unmodifiedInReducedPattern v (GenIrrefPatn (CS.PTuple ips) _ _) =
    all (unmodifiedInReducedPattern v) ips
unmodifiedInReducedPattern v (GenIrrefPatn (CS.PVar pv) _ _) = v /= pv
unmodifiedInReducedPattern v _ = True


-- | Replace some subexpressions of linear type by dummy expressions or convert NULL to readonly.
-- The first argument is a string to be prepended to the error messages.
-- If the second argument is True, convert NULL expressions to readonly instead of error.
-- The third argument is a boolean vector specifying the tuple components to be replaced,
-- if the expression is seen as a tuple.
markLinearAsError :: String -> Bool -> [Bool] -> GenExpr -> ETrav GenExpr
markLinearAsError _ _ bools e | not $ or bools = return e
markLinearAsError msgp cnvNull [True] e = do
    (isn,en) <- tryConvertNull e
    if cnvNull && isn
       then return en
       else do
           recordError $ typeMatch (orgOfGE e) msg
           return $ toDummyExpr e $ mkDummyExpr t msg
    where t = mkReadonly $ typOfGE e
          msgr = "inear expression used in readonly context"
          msg = if null msgp
                   then "L" ++ msgr
                   else msgp ++ " l" ++ msgr
markLinearAsError msgp cnvNull bools (GenExpr (CS.Tuple es) o t s) = do
    esb <- mapM (\(b,e) -> markLinearAsError msgp cnvNull [b] e) $ zip bools es
    return $ GenExpr (CS.Tuple esb) o (mkTupleType (map typOfGE esb)) s
markLinearAsError msgp cnvNull bools (GenExpr (CS.Let bs bdy) o t s) = do
    bdyb <- markLinearAsError msgp cnvNull bools bdy
    return $ GenExpr (CS.Let bs bdyb) o (typOfGE bdyb) s
markLinearAsError msgp cnvNull bools e@(GenExpr (CS.App _ _ _) _ _ _) = do
    recordError $ typeMatch (orgOfGE e) msg
    return $ toDummyExpr e $ mkDummyExpr (mkReadonly $ typOfGE e) msg
    where poss = (show $ map snd $ filter fst $ zip bools (iterate (1 +) 1))
          msgr = "inear function result used in readonly context at position(s): " ++ poss
          msg = if null msgp
                   then "L" ++ msgr
                   else msgp ++ " l" ++ msgr
markLinearAsError msgp cnvNull bools (GenExpr (CS.If e0 bvs e1 e2) o t s) = do
    e1b <- markLinearAsError msgp cnvNull bools e1
    e2b <- markLinearAsError msgp cnvNull bools e2
    return $ GenExpr (CS.If e0 bvs e1b e2b) o (typOfGE e1b) s
markLinearAsError msgp cnvNull bools (GenExpr (CS.Match e0 bvs alts) o t s) = do
    altsb <- mapM (\(CS.Alt p l e) -> do { e' <- markLinearAsError msgp cnvNull bools e; return $ CS.Alt p l e'}) alts
    let (CS.Alt _ _ e1b) = head altsb
    return $ GenExpr (CS.Match e0 bvs altsb) o (typOfGE e1b) s

-- | If the expression evaluates to NULL, convert its type to readonly.
-- The first result component is true, if conversion was successful.
-- The expression has no tuple type.
tryConvertNull :: GenExpr -> ETrav (Bool,GenExpr)
tryConvertNull e = do
      -- use changeLinToRoInExpr to determine the internal sources of e
    (eb,bvs,errs) <- runExprTrav [] $ changeLinToRoInExpr M.empty [True] e
    if (null errs) && (all isUniqueNull bvs) -- all linear sources in e are NULL
       then do
             -- use rslvRoDiffs to convert the sources to readonly
           (eb',_,_) <- runExprTrav [] $ rslvRoDiffs bvs [] M.empty eb
           return (True,eb')
       else return (False, e)

-- | Replace all occurrences of variables in a set by dummy expressions.
bangToError :: [CCS.VarName] -> GenExpr -> GenExpr
bangToError vs e = mapExprOfGE (bangToError' vs (typOfGE e)) e

bangToError' :: [CCS.VarName] -> GenType -> ExprOfGE -> ExprOfGE
bangToError' vs t e@(CS.Var v) =
    if elem v vs
       then exprOfGE $ mkDummyExpr t ("Necessary banging of " ++ v ++ " leads to non-escapeable type")
       else e
bangToError' vs _ e = fmap (bangToError vs) e

-- | Try to find variables which can be banged to resolve readonly type incompatibilities in an expression.
-- If it is not possible to resolve all readonly type incompatibilities in this way,
-- and the expression contains bang positions, it is instead processed by bangprocN to try the inner bang positions.
-- Otherwise in the monadic state a minimal set of variables is returned which must be banged.
-- Remaining incompatibilities are resolved using dummy expressions, returning corresponding error messages in the monadic state.
-- In the returned expressions all readonly type incompatibilities have been resolved.
bangprocExpr :: GenExpr -> Trav [CCS.VarName] GenExpr
bangprocExpr e = do
    (eb,bvs,errs) <- runExprTrav [] $ tryBangExpr e
    if (not $ null errs) && (hasInnerBangPositions $ exprOfGE e)
       then do
           (ep,(),errp) <- runExprTrav () $ bangprocN e -- try to bang only parts of e
           mapM recordError errp
           return ep
       else do
           mapM recordError errs
           modifyUserState (\tvs -> union tvs $ filter (not . isUniqueNull) bvs)
           return eb

-- | Does an expression contain syntactic possibilities for banging variables.
-- This is the case if it contains subexpressions of kind Let, If, Match, MultiWayIf.
-- Match and MultiWayIf are not checked because they are not generated.
hasInnerBangPositions :: ExprOfGE -> Bool
hasInnerBangPositions (CS.Let _ _) = True
hasInnerBangPositions (CS.If _ _ _ _) = True
hasInnerBangPositions (CS.PrimOp _ es) = any (hasInnerBangPositions . exprOfGE) es
hasInnerBangPositions (CS.Upcast e) = hasInnerBangPositions $ exprOfGE e
hasInnerBangPositions (CS.Tuple es) = any (hasInnerBangPositions . exprOfGE) es
hasInnerBangPositions (CS.App e1 e2 _) = (hasInnerBangPositions $ exprOfGE e1) || (hasInnerBangPositions $ exprOfGE e2)
hasInnerBangPositions (CS.Match e0 _ alts) = (hasInnerBangPositions $ exprOfGE e0)
    || any (\(CS.Alt _ _ e) -> hasInnerBangPositions $ exprOfGE e) alts
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
getExprSources vmap (CS.Match _ _ alts) =
    map (nub . concat) $ transpose $ map (\(CS.Alt _ _ e) -> getExprSources vmap $ exprOfGE e) alts
getExprSources vmap (CS.Tuple es) = concatMap ((getExprSources vmap) . exprOfGE) es
getExprSources vmap (CS.Put e pts) = getExprSources vmap $ exprOfGE e
getExprSources vmap (CS.ArrayPut e pts) = getExprSources vmap $ exprOfGE e
getExprSources vmap (CS.Let bs bdy) = getExprSources (addVarSourcesFromBindings vmap bs) $ exprOfGE bdy
getExprSources vmap (CS.App f e _) =
    case typeOfGT $ getResultType $ typOfGE f of
         CS.TTuple ts -> map (const []) ts
         _ -> if isMayNullOperation f
                 then getExprSources vmap $ exprOfGE e
                 else [[]]
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

isMayNullOperation :: GenExpr -> Bool
isMayNullOperation (GenExpr (CS.TLApp f _ _ _) _ _ _) | elem f ["mayNull","notNull"] = True
isMayNullOperation _ = False

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
-- (todo) here we assume that generated match expressions always have two alternatives
rslvRoDiffs vs cvs vmap (GenExpr (CS.Match e0 bvs [CS.Alt p1 l1 e1, CS.Alt p2 l2 e2]) o t s) = do
    e0b <- rslvRoDiffs vs cvs vmap e0
    e1b <- rslvRoDiffs vs cvs vmap e1
    e2b <- rslvRoDiffs vs cvs vmap e2
    (e1bm,e2bm,tm) <- matchRoExprs vmap e1b e2b
    let alt1 = CS.Alt (bangInPatn vs vmap p1) l1 e1bm
        alt2 = CS.Alt (bangInPatn vs vmap p2) l2 e2bm
    return $ GenExpr (CS.Match e0b bvs [alt1, alt2]) o tm s
rslvRoDiffs vs cvs vmap (GenExpr (CS.App f e infx) o t s) | isMayNullOperation f = do
    eb <- rslvRoDiffs vs cvs vmap e
    let (tbs,ebs) = matchRoTypes (getParamType $ typOfGE f) $ typOfGE eb
    ebm <- changeLinToRoInExpr vmap ebs eb
    let fb = if head tbs then bangMayNullOperation f else f
        tb = getResultType $ typOfGE fb
    return $ GenExpr (CS.App fb ebm infx) o tb s
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
rslvRoDiffs vs cvs vmap (GenExpr (CS.Lam ip lt e) o t s) = do
    eb <- rslvRoDiffs [] [] M.empty e -- all free variables in e must be bound in ip
    return (GenExpr (CS.Lam ip lt eb) o (mkFunType (getParamType t) (typOfGE eb)) s)
-- for all other expressions occurring here a recursive application will not change the type
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
    ipbm <- cmpNotModified cvs ipb $ isPutExpr $ exprOfGE e
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

-- | Bang variable types in a (refutable) pattern.
-- The pattern is either "Nothing" or "Some v" where v is a C or component variable.
-- The first argument is a list of variables for which the type must be banged at every occurrence.
-- The second argument is the variable source map for all variables of linear type bound in the context.
-- The variables are banged according to their own source variables.
bangInPatn :: [CCS.VarName] -> VarSourceMap -> GenPatn -> GenPatn
bangInPatn vs vmap (GenPatn (CS.PCon tn ips) o t) =
    GenPatn (CS.PCon tn (map (bangInPattern vs vmap []) ips)) o $ mkReadonly t
bangInPatn _ _ p = p

bangMayNullOperation :: GenExpr -> GenExpr
bangMayNullOperation (GenExpr (CS.TLApp f mt ml il) o (GenType (CS.TFun pt rt) ot _) c) =
    GenExpr (CS.TLApp f (map (fmap mkReadonly) mt) ml il) o (GenType (CS.TFun (mkReadonly pt) (mkReadonly rt)) ot Nothing) c


-- | Check whether a variable is modified by a pattern.
-- The first argument is a list of variables which may not be modified.
-- If it occurs in the pattern it is replaced by the error variable and an error is recorded.
cmpNotModified :: [CCS.VarName] -> GenIrrefPatn -> [Bool] ->Trav [CCS.VarName] GenIrrefPatn
cmpNotModified cvs ip@(GenIrrefPatn (CS.PVar pv) o t) [False] | elem pv cvs = do
    recordError $ typeMatch o "Component of readonly struct modified"
    return $ GenIrrefPatn (CS.PVar errVar) o t
cmpNotModified cvs (GenIrrefPatn (CS.PTuple ips) o t) isputs = do
    ipsm <- mapM (\(ip,isput) -> cmpNotModified cvs ip [isput]) $ zip ips isputs
    return $ GenIrrefPatn (CS.PTuple ipsm) o t
cmpNotModified _ ip _ = return ip

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
-- The returned type is banged in every component where, after matching, both expressions have readonly type.
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
    return $ GenExpr (CS.If e0 bvs e1b e2b) o (adaptTypes (typOfGE e1b) (typOfGE e2b)) s
markReadonlyAsError bools t (GenExpr (CS.Match e0 bvs alts) o _ s) = do
    altsb <- mapM (\(CS.Alt p l e) -> do {e' <- markReadonlyAsError bools t e; return $ CS.Alt p l e'}) alts
    let tm = foldl1' adaptTypes $ map (\(CS.Alt _ _ e) -> typOfGE e) altsb
    return $ GenExpr (CS.Match e0 bvs altsb) o tm s

-- | Change some subexpressions of linear type to readonly type.
-- The second argument is a boolean vector specifying the tuple components to be changed,
-- if the expression is seen as a tuple.
-- If a component is no variable or has no source variables it is replaced by a dummy expression of the readonly type and an error is recorded.
-- Otherwise its source variables are added to the state and the expression is returned.
changeLinToRoInExpr :: VarSourceMap -> [Bool] -> GenExpr -> Trav [CCS.VarName] GenExpr
changeLinToRoInExpr _ bools e | not $ or bools = return e
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
    return $ GenExpr (CS.If e0 bvs e1b e2b) o (adaptTypes (typOfGE e1b) (typOfGE e2b)) s
changeLinToRoInExpr vmap bools (GenExpr (CS.Match e0 bvs alts) o t s) = do
    altsb <- mapM (\(CS.Alt p l e) -> do {e' <- changeLinToRoInExpr vmap bools e; return $ CS.Alt p l e'}) alts
    let tm = foldl1' adaptTypes $ map (\(CS.Alt _ _ e) -> typOfGE e) altsb
    return $ GenExpr (CS.Match e0 bvs altsb) o tm s
changeLinToRoInExpr vmap [True] e@(GenExpr (CS.Var v) _ _ _) | not $ null $ getVarSources vmap v = do
    recordSources vmap v
    return e
changeLinToRoInExpr vmap [True] e = do
    recordError $ typeMatch (orgOfGE e) msg
    return $ toDummyExpr e $ mkDummyExpr t msg
    where t = mkReadonly $ typOfGE e
          msg = "Linear expression used in readonly context"

-- | Change some linear type components to readonly to resolve incompatibilities between two types.
-- The first and second arguments are boolean vectors specifying the type components to be changed,
-- if the types are seen as tuple types.
-- The result consists of all adapted types from changed components and the remaining components.
changeLinToRoInTypes :: [Bool] -> [Bool] -> GenType -> GenType -> GenType
changeLinToRoInTypes [b1] [b2] t1 t2 =
    adaptTypes (if b1 then mkReadonly t1 else t1) (if b2 then mkReadonly t2 else t2)
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

{- Try to bang additional linear variables -}
{- of container types                      -}
{-------------------------------------------}

ebangproc :: GenExpr -> ETrav GenExpr
ebangproc e = do
    (eN,_,_) <- runExprTrav 0 $ mkNullUnique e
    eN' <- ebangprocN eN
    reNullUnique eN'

ebangprocN :: GenExpr -> ETrav GenExpr
ebangprocN e = mapMExprOfGE ebangproc' e

-- | Try to bang additional variables in subexpressions where that is possible.
-- Banging is possible in conditions of conditional expressions and in bindings.
-- No bang tried in CS.Match, because generated match expressions for NULL test would never be escapeable when banged.
-- No bang tried in CS.LamC, CS.MultiWayIf, because these are not generated.
-- Since variables are only banged in sub-contexts, and the effects may not escape these sub-contexts,
-- the type of the expression remains unchanged.
ebangproc' :: ExprOfGE -> ETrav ExprOfGE
ebangproc' (CS.Let bs bdy) = do
    bsb <- ebangprocInLet bs $ exprOfGE bdy
    bdyp <- ebangprocN bdy
    return $ CS.Let bsb bdyp
ebangproc' (CS.If e bvs e1 e2) = do
    -- type of e is always escapeable because it is boolean
    (ebe,bvse) <- extendBangExpr e bvs
    e1p <- ebangprocN e1
    e2p <- ebangprocN e2
    return $ CS.If ebe bvse e1p e2p
ebangproc' e = mapM ebangprocN e

-- | Try to bang additional variables in the bindings of a let expressions.
-- The let body is required to determine the variables used in it, it is not processed.
-- Bindings are processed in their order in the let expression.
ebangprocInLet :: [GenBnd] -> ExprOfGE -> ETrav [GenBnd]
ebangprocInLet [] _ = return []
ebangprocInLet bs bdy = do
    (bb : bsr) <- ebangprocInBindings bs bdy
    bsrp <- ebangprocInLet bsr bdy
    return (bb : bsrp)

-- | Try to bang additional variables in a prefix of a binding sequence.
-- The shortest prefix is used for which the result is escapeable.
-- If successful, the prefix is converted to a single binding with banged variables.
-- This binding binds (only) the variables which occur free in the remaining bindings followed by the expression.
-- Otherwise the sequence is returned unmodified.
ebangprocInBindings :: [GenBnd] -> ExprOfGE -> ETrav [GenBnd]
ebangprocInBindings [] _ = return []
ebangprocInBindings (b@(CS.Binding ip m e bvs):bs) bdy = do
           (ipre,ebre,bvse) <- extendBangBinding ip e bvs
           ebrebbb <- if (hasInnerBangPositions $ exprOfGE ebre)
                         then ebangprocN ebre
                         else return ebre
           bsb <- ebangprocInBindings bs bdy
           return ((CS.Binding ipre m ebrebbb bvse) : bsb)

-- | Try to bang additional variables in an expression.
-- Candidates are all free variables which occur as container with linear type in a take operation.
-- The result is the expression with additional types banged and the extended set of variables to bang.
extendBangExpr :: GenExpr -> [CCS.VarName] -> ETrav (GenExpr, [CCS.VarName])
extendBangExpr e vs = do
    (eb,bvs) <- extendBangVars e $ getBangCandidates [] e
    return (eb,union vs $ filter (not . isUniqueNull) bvs)

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

-- | Try to bang additional variables in a bound expression.
-- Candidates are all free variables which occur as container with linear type in a take operation.
-- Successfully banged variables are removed from the expression result and the binding pattern.
-- Returned are the new pattern, the expression with additional types banged and the extended set of variables to bang.
-- The remaining component types in the pattern are unchanged.
extendBangBinding :: GenIrrefPatn -> GenExpr -> [CCS.VarName] -> ETrav (GenIrrefPatn, GenExpr, [CCS.VarName])
extendBangBinding ip e vs = do
    (ipb,eb,bvs) <- extendBangBindingVars ip e $ getBangCandidates [] e
    return (ipb,eb,union vs $ filter (not . isUniqueNull) bvs)

-- | Try to change variable types to readonly in an expression according to a list of typed variables.
-- Variables with successfully changed type are removed from the expression result and the binding pattern.
-- eturned are the new pattern and expression together with the list of all variables
-- where the type has been successfully changed.
extendBangBindingVars :: GenIrrefPatn -> GenExpr -> [CCS.VarName] -> ETrav (GenIrrefPatn, GenExpr, [CCS.VarName])
extendBangBindingVars ip e [] = return (ip,e,[])
extendBangBindingVars ip e (v:vs) = do
    (eb,bvs,errs) <- runExprTrav [] $ bangVars [v] e
    let (ipr,ebr) = reduceBangedBinding bvs ip eb
    if null errs && (mayEscape $ typOfGE ebr)
       then do
           (iprb,ebb,bbvs) <- extendBangBindingVars ipr ebr (vs \\ bvs)
           return (iprb, ebb, union bbvs bvs)
       else extendBangBindingVars ip e vs

-- | Return all free variables which occur as container with linear type in a take operation.
-- The first argument is the list of all variables not free or already banged in the expression.
getBangCandidates :: [CCS.VarName] -> GenExpr -> [CCS.VarName]
getBangCandidates nfvs (GenExpr (CS.Let bs bdy) _ _ _) =
    union (getBangCandInBindings nfvs bs) (getBangCandidates (union nfvs $ boundInBindings bs) bdy)
getBangCandidates nfvs (GenExpr (CS.Lam ip mt bdy) _ _ _) =
    getBangCandidates (union nfvs $ freeInIrrefPatn ip) bdy
getBangCandidates nfvs (GenExpr (CS.If e0 bvs e1 e2) _ _ _) =
    union (getBangCandidates (union bvs nfvs) e0) $
        union (getBangCandidates nfvs e1) (getBangCandidates nfvs e2)
getBangCandidates nfvs (GenExpr (CS.Match e bvs alts) _ _ _) =
    union (getBangCandidates (union bvs nfvs) e) $
       nub $ concat $ map (\(CS.Alt p l e) -> getBangCandidates nfvs e) alts
getBangCandidates nfvs e = nub $ concat $ fmap (getBangCandidates nfvs) $ exprOfGE e -- banging applies also to alts!

-- | Return all free variables which occur as container with linear type in a take operation.
-- The first argument is the list of all variables not free or already banged in the bindings.
getBangCandInBindings :: [CCS.VarName] -> [GenBnd] -> [CCS.VarName]
getBangCandInBindings _ [] = []
getBangCandInBindings nfvs ((CS.Binding ip _ e bvs):bs) =
    union (union (getBangCandInPattern nfvs ip) (getBangCandidates (union bvs nfvs) e))
        $ getBangCandInBindings (union nfvs $ freeInIrrefPatn ip) bs

-- | Return all free variables which occur as container with linear type in a take operation and are not the error variable.
-- The first argument is the list of all variables not free or already banged in the bound expression.
getBangCandInPattern :: [CCS.VarName] -> GenIrrefPatn -> [CCS.VarName]
getBangCandInPattern nfvs (GenIrrefPatn (CS.PTake pv [Just (_,(GenIrrefPatn (CS.PVar cv) _ _))]) _ t)
    | (not $ elem pv nfvs) && (not $ isNonlinear t) && (pv /= errVar) = [pv]
getBangCandInPattern nfvs (GenIrrefPatn (CS.PArrayTake pv [(_,(GenIrrefPatn (CS.PVar cv) _ _))]) _ t)
    | (not $ elem pv nfvs) && (not $ isNonlinear t) && (pv /= errVar) = [pv]
getBangCandInPattern nfvs (GenIrrefPatn (CS.PTuple ips) _ _) = nub $ concat $ map (getBangCandInPattern nfvs) ips
getBangCandInPattern _ _ = []

{- Matching MayNull subexpressions          -}
{- to not-null context: exploit NULL-tests  -}
{- Convert not-null subexpressions          -}
{- to MayNull context.                      -}
{--------------------------------------------}

maynullproc :: GenExpr -> ETrav GenExpr
maynullproc e = do
    let e1 = sepNullTests e
    -- extend take/put scopes for MayNull components here
    rslvMayNullDiffs $ convNullTests [] e1

-- | Split conditional expressions to separate NULL tests from other conditions.
sepNullTests :: GenExpr -> GenExpr
sepNullTests (GenExpr (CS.Let bs bdy) o t c) =
    if null bs' then bdy' else GenExpr (CS.Let (reverse bs') bdy') o t c
    where (bs',bdy') = sepNullTestsInLet [] bs bdy
sepNullTests e = mapExprOfGE (fmap sepNullTests) e

-- | Split conditional expressions in a let context
-- The first argument is the reversed list of processed bindings.
-- The second argument is the list of bindings to be processed.
-- The result is the reversed list of remaining processed bindings and the processed body.
sepNullTestsInLet :: [GenBnd] -> [GenBnd] -> GenExpr -> ([GenBnd],GenExpr)
sepNullTestsInLet cbs (CS.Binding ip mt e bvs : bs) bdy =
    sepNullTestsInLet ((CS.Binding ip mt (sepNullTests e) bvs) : cbs) bs bdy
sepNullTestsInLet cbs [] e@(GenExpr (CS.If e0 bvs e1 e2) o t c)
    | (not $ withoutNullTest cbs $ exprOfGE e0) && (not $ isNullTest cbs $ exprOfGE e0)
    = splitByNullTests cbs (GenExpr (CS.If e0 bvs e1' e2') o t c)
    where e1' = sepNullTests e1
          e2' = sepNullTests e2
sepNullTestsInLet cbs [] e = (cbs, sepNullTests e)

-- | Split a conditional expression.
-- The first argument is the reversed list of bindings with all structure used in the condition.
-- The expression must be a conditional expression.
-- Its condition has either type Bool or a tuple type where the first component is Bool.
-- The expression branches and the expressions bound in the bindings have already been processed.
-- The result is the expression with split condition
-- and the reversed list of bindings without the bindings consumed for splitting the condition.
-- If branches of the expression have been duplicated by splitting,
-- bindings may have been extracted and added to the returned list.
splitByNullTests :: [GenBnd] -> GenExpr -> ([GenBnd],GenExpr)
splitByNullTests cbs e@(GenExpr (CS.If _ bvs e1 e2) o t c) | (CS.Var v) <- getCond' e =
    case findBindingFor cbs v of
         Nothing -> (cbs, e)
         Just (b@(CS.Binding ip _ e0 _),bsb,bsa) ->
            if exchangeableWithBindings b bsb
               then splitByNullTests (bsb++bsa) $ GenExpr (CS.If e0 bvs e1 e2) o t c
               else (cbs, e)
splitByNullTests cbs e@(GenExpr (CS.If _ bvs e1 e2) o t c) | (CS.Let bs bdy) <- getCond' e =
    splitByNullTests ((reverse bs)++cbs) $ GenExpr (CS.If bdy bvs e1 e2) o t c
splitByNullTests cbs e@(GenExpr (CS.If _ bvs e1 e2) o t c) | (CS.Tuple es) <- getCond' e =
    splitByNullTests cbs $ GenExpr (CS.If (head es) bvs e1 e2) o t c
splitByNullTests cbs e@(GenExpr (CS.If _ bvs e1 e2) o t c) | (CS.PrimOp op [e0]) <- getCond' e, op == "not" =
    splitByNullTests cbs $ GenExpr (CS.If e0 bvs e2 e1) o t c
splitByNullTests cbs e | (CS.If _ _ _ _) <- getCond' e =
    let (ebs,e') = unfoldCondition cbs e
    in ((reverse ebs)++cbs, e')
splitByNullTests cbs e = error ("Unexpected expression in splitByNullTests: " ++ (show e))

-- | Unfold a condition in a conditional expression.
-- The expression must be a conditional expression.
-- Its condition has either type Bool or a tuple type where the first component is Bool.
-- It has already been split and contains no negations.
-- The first argument is the reversed list of bindings with all structure used in the condition.
-- The result is the transformed expression
-- with possibly additional (unreversed) bindings extracted from the branches.
unfoldCondition :: [GenBnd] -> GenExpr -> ([GenBnd],GenExpr)
unfoldCondition cbs (GenExpr (CS.If (GenExpr e0' _ _ _) _ e1 e2) _ _ _) | isTrueConst cbs e0' = ([], e1)
unfoldCondition cbs (GenExpr (CS.If (GenExpr e0' _ _ _) _ e1 e2) _ _ _) | isFalseConst cbs e0' = ([], e2)
unfoldCondition cbs (GenExpr (CS.If (GenExpr e0'@(CS.If d0 dbvs d1 d2) od td cd) bvs e1 e2) o t c) =
    let (ebs,r1,r2) = extractBindings (freeInExpr' e0') (branchCopies cbs e0') e1 e2
        (bs1',e1') = unfoldCondition ((reverse ebs)++cbs) $ GenExpr (CS.If d1 bvs r1 r2) o t c
        (bs2',e2') = unfoldCondition ((reverse ebs)++cbs) $ GenExpr (CS.If d2 bvs r1 r2) o t c
    in (ebs, GenExpr (CS.If d0 dbvs (mkSafeLetExpr bs1' e1') (mkSafeLetExpr bs2' e2')) od td cd)
unfoldCondition cbs (GenExpr (CS.If (GenExpr (CS.Let bs0 bdy) od td cd) bvs e1 e2) o t c) =
    let (bs',e') = unfoldCondition ((reverse bs0)++cbs) $ GenExpr (CS.If bdy bvs e1 e2) o t c
    in (bs0++bs',e')
unfoldCondition cbs (GenExpr (CS.If (GenExpr (CS.Tuple es) _ _ _) bvs e1 e2) o t c) =
    unfoldCondition cbs (GenExpr (CS.If (head es) bvs e1 e2) o t c)
unfoldCondition cbs e = ([], e)

getCond :: GenExpr -> GenExpr
getCond (GenExpr (CS.If e _ _ _) _ _ _) = e
getCond _ = mkUnitExpr

getCond' = exprOfGE . getCond

mkSafeLetExpr :: [GenBnd] -> GenExpr -> GenExpr
mkSafeLetExpr [] e = e
mkSafeLetExpr bs e = mkLetExpr bs e

-- | Search the binding for a value variable in a binding list.
-- If not found the result is Nothing.
-- Otherwise the result is the binding, and the binding lists before and after it in the original list.
findBindingFor :: [GenBnd] -> VarName -> Maybe (GenBnd, [GenBnd], [GenBnd])
findBindingFor [] v = Nothing
findBindingFor (b@(CS.Binding (GenIrrefPatn (CS.PVar pv) _ _) _ _ _) : bs) v | pv == v = Just (b,[],bs)
findBindingFor (b@(CS.Binding (GenIrrefPatn (CS.PTuple ((GenIrrefPatn (CS.PVar pv) _ _) : _ )) _ _) _ _ _) : bs) v | pv == v = Just (b,[],bs)
findBindingFor (b : bs) v =
    case findBindingFor bs v of
         Nothing -> Nothing
         Just (fb,bsb,bsa) -> Just (fb, (b : bsb), bsa)

unfoldValVar :: [GenBnd] -> VarName -> Maybe GenExpr
unfoldValVar cbs v =
    case findBindingFor cbs v of
         Nothing -> Nothing
         Just ((CS.Binding _ _ e _),_,_) -> Just e

-- | Extract bindings from two expressions so that they retain their semantics.
-- Bindings are only extracted from an expression
--   if it is a let expression, the corresponding Int is > 1,
--   and the bound variables are disjoint with the give set of variables.
-- A binding is only extracted from one expression if no bound variable occurs free in the other expression.
extractBindings :: [VarName] -> (Int,Int) -> GenExpr -> GenExpr -> ([GenBnd],GenExpr,GenExpr)
extractBindings fvs (i1,i2) (GenExpr (CS.Let (b@(CS.Binding ip _ e _) : bs1) bdy1) o1 t1 c1) e2
    | i1 > 1 && (null $ intersect (freeInIrrefPatn ip) vs')
    = (b : bs, r1, r2)
    where vs' = union fvs $ freeInExpr e2
          e1' = if null bs1 then bdy1 else GenExpr (CS.Let bs1 bdy1) o1 t1 c1
          (bs,r1,r2) = extractBindings fvs (i1,i2) e1' e2
extractBindings fvs (i1,i2) e1 (GenExpr (CS.Let (b@(CS.Binding ip _ _ _) : bs2) bdy2) o2 t2 c2)
    | i2 > 1 && (null $ intersect (freeInIrrefPatn ip) vs')
    = (b : bs, r1, r2)
    where vs' = union fvs $ freeInExpr e1
          e2' = if null bs2 then bdy2 else GenExpr (CS.Let bs2 bdy2) o2 t2 c2
          (bs,r1,r2) = extractBindings fvs (i1,i2) e1 e2'
extractBindings _ _ e1 e2 = ([],e1,e2)

-- | Number of copies for then and else branch required for splitting the condition.
branchCopies :: [GenBnd] -> ExprOfGE -> (Int,Int)
branchCopies cbs (CS.Tuple es) = branchCopies cbs $ exprOfGE $ head es
branchCopies cbs e | isTrueConst cbs e = (1,0)
branchCopies cbs e | isFalseConst cbs e = (0,1)
branchCopies cbs e | withoutNullTest cbs e || isNullTest cbs e = (1,1)
branchCopies cbs (CS.If e0 _ e1 e2) =
    addPair (mulPair bx $ capPair $ branchCopies cbs $ exprOfGE e1)
            (mulPair by $ capPair $ branchCopies cbs $ exprOfGE e2)
    where (bx,by) = branchCopies cbs $ exprOfGE e0
branchCopies cbs (CS.PrimOp op [e]) | op == "not" = (by,bx)
    where (bx,by) = branchCopies cbs $ exprOfGE e
branchCopies cbs (CS.Var v) = maybe (1,1) ((branchCopies cbs) . exprOfGE) $ unfoldValVar cbs v
branchCopies cbs (CS.Let bs bdy) = branchCopies ((reverse bs) ++ cbs) $ exprOfGE bdy
branchCopies cbs e = (1,1)

capPair :: (Int, Int) -> (Int, Int)
capPair (i,j) = (if i > 0 then 1 else 0, if j > 0 then 1 else 0)

mulPair :: Int -> (Int,Int) -> (Int,Int)
mulPair i (j,k) = (i*j, i*k)

addPair :: (Int,Int) -> (Int,Int) -> (Int,Int)
addPair (i1,j1) (i2,j2) = (i1+i2,j1+j2)

withoutNullTest :: [GenBnd] -> ExprOfGE -> Bool
withoutNullTest cbs (CS.Tuple es) = withoutNullTest cbs $ exprOfGE $ head es
withoutNullTest cbs e | isTrueConst cbs e || isFalseConst cbs e = True
withoutNullTest cbs e | isNullTest cbs e = False
withoutNullTest cbs (CS.PrimOp op [e]) | op == "not" = withoutNullTest cbs $ exprOfGE e
withoutNullTest cbs (CS.If e0 _ e1 e2) = all ((withoutNullTest cbs) . exprOfGE) [e0, e1, e2]
withoutNullTest cbs (CS.Var v) = maybe True ((withoutNullTest cbs) . exprOfGE) $ unfoldValVar cbs v
withoutNullTest cbs (CS.Let bs bdy) = withoutNullTest ((reverse bs) ++ cbs) $ exprOfGE bdy
withoutNullTest _ _ = True

isNullTest :: [GenBnd] -> ExprOfGE -> Bool
isNullTest cbs (CS.Tuple es) = isNullTest cbs $ exprOfGE $ head es
isNullTest cbs (CS.PrimOp op es) | elem op ["==","/="] = any ((isNullConst cbs) . exprOfGE) es
isNullTest cbs (CS.Var v) = maybe False ((isNullTest cbs) . exprOfGE) $ unfoldValVar cbs v
isNullTest cbs (CS.Let bs bdy) = isNullTest ((reverse bs) ++ cbs) $ exprOfGE bdy
isNullTest _ _ = False

isNullConst :: [GenBnd] -> ExprOfGE -> Bool
isNullConst cbs (CS.Var v) = v == mapNull || (maybe False ((isNullConst cbs) . exprOfGE) $ unfoldValVar cbs v)
isNullConst cbs (CS.Let bs bdy) = isNullConst ((reverse bs) ++ cbs) $ exprOfGE bdy
isNullConst cbs (CS.Tuple es) = isNullConst cbs $ exprOfGE $ head es
isNullConst _ _ = False

isTrueConst :: [GenBnd] -> ExprOfGE -> Bool
isTrueConst _ (CS.BoolLit b) = b
isTrueConst cbs (CS.Var v) = (maybe False ((isTrueConst cbs) . exprOfGE) $ unfoldValVar cbs v)
isTrueConst cbs (CS.Let bs bdy) = isTrueConst ((reverse bs) ++ cbs) $ exprOfGE bdy
isTrueConst cbs (CS.Tuple es) = isTrueConst cbs $ exprOfGE $ head es
isTrueConst _ _ = False

isFalseConst :: [GenBnd] -> ExprOfGE -> Bool
isFalseConst _ (CS.BoolLit b) = not b
isFalseConst cbs (CS.Var v) = (maybe False ((isFalseConst cbs) . exprOfGE) $ unfoldValVar cbs v)
isFalseConst cbs (CS.Let bs bdy) = isFalseConst ((reverse bs) ++ cbs) $ exprOfGE bdy
isFalseConst cbs (CS.Tuple es) = isFalseConst cbs $ exprOfGE $ head es
isFalseConst _ _ = False

-- | Convert conditional expressions with a NULL test as condition to a match expression using notNull.
-- In the Some branch change type of tested variable from MayNull wrapped to unwrapped.
-- If the tested variable already has not-null type simplify the conditional expression to its then branch.
-- The first argument is a reversed context binding list to resolve variables involved in a NULL test.
convNullTests :: [GenBnd] -> GenExpr -> GenExpr
convNullTests cbs (GenExpr (CS.If e0 [] e1 e2) o _ c) =
    let e1' = convNullTests cbs e1
        e2' = convNullTests cbs e2
        e' = GenExpr (CS.If e0 [] e1' e2') o (adaptTypes (typOfGE e1') (typOfGE e2')) c
    in if isNullTest cbs $ exprOfGE e0
          then case convNullTest cbs e' of
                    Nothing -> e'
                    Just e'' -> e''
          else e'
convNullTests cbs (GenExpr (CS.Let bs bdy) o _ c) =
    GenExpr (CS.Let bs' bdy') o (typOfGE bdy') c
    where (bs',bdy') = convNullTestsInLet cbs bs bdy
convNullTests cbs (GenExpr (CS.Lam ip mt bdy) o t c) =
    GenExpr (CS.Lam ip mt e') o (mkFunType (getParamType t) (typOfGE e')) c
    where e' = convNullTests [] bdy
convNullTests cbs (GenExpr (CS.App f e infx) o _ c) =
    GenExpr (CS.App f' e' infx) o (getResultType $ typOfGE f') c
    where f' = convNullTests cbs f
          e' = convNullTests cbs e
convNullTests cbs (GenExpr (CS.Tuple es) o _ c) =
    GenExpr (CS.Tuple es') o (mkTupleType $ map typOfGE es') c
    where es' = map (convNullTests cbs) es
convNullTests cbs e = mapExprOfGE (fmap (convNullTests cbs)) e

convNullTestsInLet :: [GenBnd] -> [GenBnd] -> GenExpr -> ([GenBnd],GenExpr)
convNullTestsInLet cbs [] bdy = ([], convNullTests cbs bdy)
convNullTestsInLet cbs (CS.Binding ip mt e bvs : bs) bdy =
    (b' : bs'', bdy'')
    where e' = convNullTests cbs e
          (ip',tvs) = fixTypeOfBound ip (typOfGE e) (typOfGE e')
          (bs',bdy') = setTypeOfVarsInLet tvs bs bdy
          b' = CS.Binding ip' mt e' bvs
          (bs'',bdy'') = convNullTestsInLet (b' : cbs) bs' bdy'

convNullTest :: [GenBnd] -> GenExpr -> Maybe GenExpr
convNullTest cbs e@(GenExpr (CS.If _ bvs e1 e2) o t c) | (CS.Var v) <- getCond' e =
    case findBindingFor cbs v of
         Nothing -> Nothing
         Just (b@(CS.Binding _ _ e0' _),bsb,bsa) ->
            if exchangeableWithBindings b bsb
               then convNullTest (bsb++bsa) $ GenExpr (CS.If e0' bvs e1 e2) o t c
               else Nothing
convNullTest cbs e@(GenExpr (CS.If _ bvs e1 e2) o t c) | (CS.Tuple es) <- getCond' e =
    convNullTest cbs $ GenExpr (CS.If (head es) bvs e1 e2) o t c
convNullTest cbs e@(GenExpr (CS.If _ bvs e1 e2) o t c) | (CS.Let bs bdy) <- getCond' e =
    convNullTest ((reverse bs)++cbs) $ GenExpr (CS.If bdy bvs e1 e2) o t c
convNullTest cbs e@(GenExpr (CS.If _ bvs e1 e2) o t c)
    | (GenExpr (CS.PrimOp op es) co ct cc) <- getCond e, op == "==" =
    convNullTest cbs $ GenExpr (CS.If (GenExpr (CS.PrimOp "/=" es) co ct cc) bvs e2 e1) o t c
convNullTest cbs e@(GenExpr (CS.If _ bvs e1 e2) o t c)
    | (GenExpr (CS.PrimOp op [a1,a2]) co ct cc) <- getCond e, isNullConst cbs $ exprOfGE a1 =
    convNullTest cbs $ GenExpr (CS.If (GenExpr (CS.PrimOp op [a2,a1]) co ct cc) bvs e1 e2) o t c
convNullTest cbs e@(GenExpr (CS.If _ bvs e1 e2) o t c)
    | (GenExpr (CS.PrimOp op [GenExpr (CS.Var v) _ _ _, a2]) co ct cc) <- getCond e, isValVar v =
    case findBindingFor cbs v of
         Nothing -> Nothing
         Just (b@(CS.Binding ip _ e0' _),bsb,bsa) ->
            if exchangeableWithBindings b bsb
               then convNullTest (bsb++bsa) $ GenExpr (CS.If (GenExpr (CS.PrimOp op [e0', a2]) co ct cc) bvs e1 e2) o t c
               else Nothing
convNullTest cbs e@(GenExpr (CS.If _ bvs e1 e2) o t c)
    | (GenExpr (CS.PrimOp op [GenExpr (CS.Tuple es) _ _ _, a2]) co ct cc) <- getCond e =
    convNullTest cbs $ GenExpr (CS.If (GenExpr (CS.PrimOp op [head es, a2]) co ct cc) bvs e1 e2) o t c
convNullTest cbs e@(GenExpr (CS.If _ bvs e1 e2) o t c)
    | (GenExpr (CS.PrimOp op [GenExpr (CS.Let bs bdy) _ _ _, a2]) co ct cc) <- getCond e =
    convNullTest ((reverse bs)++cbs) $ GenExpr (CS.If (GenExpr (CS.PrimOp op [bdy, a2]) co ct cc) bvs e1 e2) o t c
convNullTest cbs e@(GenExpr (CS.If _ bvs e1 e2) o t c)
    | (GenExpr (CS.PrimOp op [a1, a2]) co ct cc) <- getCond e, (GenExpr (CS.Var v) _ vt _) <- a1 =
    let ntype = getNnlType vt
        otype = mkOption ntype
        nvar = TV v ntype
        me = mkAppExpr (mkTopLevelFunExpr ("notNull",mkFunType vt otype) [Just ntype]) a1
        e1' = setTypeOfFree nvar e1
    in if isMayNull vt
          then Just $ mkMatchExpr o (adaptTypes (typOfGE e1') (typOfGE e2)) c me
                        [("Nothing", [], e2),
                         ("Some", [mkVarPattern nvar], e1')]
          else Just e1
convNullTest _ e = Nothing

-- | Set the type for every free occurrence of a variable in an expression.
-- And also for every value variable bound to a free occurrence of the variable.
-- And also for free occurrences after a take/put binding with the variale as container.
-- And recalculate all types of composite expressions.
setTypeOfFree :: TypedVar -> GenExpr -> GenExpr
setTypeOfFree (TV v vt) (GenExpr (CS.Var w) o _ c) | v == w = GenExpr (CS.Var w) o vt c
setTypeOfFree tv (GenExpr (CS.Tuple es) o _ c) =
    GenExpr (CS.Tuple es') o (mkTupleType (map typOfGE es')) c
    where es' = map (setTypeOfFree tv) es
setTypeOfFree tv (GenExpr (CS.App f e i) o t c) =
    GenExpr (CS.App f (setTypeOfFree tv e) i) o t c -- no change possible in f and thus in t
setTypeOfFree tv (GenExpr (CS.If e0 bvs e1 e2) o _ c) =
    GenExpr (CS.If e0' bvs e1' e2') o (adaptTypes (typOfGE e1') (typOfGE e2')) c
    where e0' = setTypeOfFree tv e0
          e1' = setTypeOfFree tv e1
          e2' = setTypeOfFree tv e2
setTypeOfFree tv (GenExpr (CS.Match e bvs alts) o t c) =
    GenExpr (CS.Match e' bvs alts') o t' c
    where e' = setTypeOfFree tv e
          alts' = map (\(CS.Alt p l e) -> CS.Alt p l $ setTypeOfFree tv e) alts
          t' = foldl1' adaptTypes $ map (\(CS.Alt p _ e) -> typOfGE e) alts'
setTypeOfFree tv e@(GenExpr (CS.Lam _ _ _) _ _ _) = e
setTypeOfFree tv (GenExpr (CS.Put e mfs) o _ c) =
    GenExpr (CS.Put e' mfs') o (typOfGE e') c
    where e' = setTypeOfFree tv e
          mfs' = map (fmap (\(f,e) -> (f,setTypeOfFree tv e))) mfs
setTypeOfFree tv (GenExpr (CS.Let bs bdy) o _ c) =
    GenExpr (CS.Let bs' bdy') o (typOfGE bdy') c
    where (bs', bdy') = setTypeOfFreeInLet tv bs bdy
setTypeOfFree tv e = mapExprOfGE (fmap (setTypeOfFree tv)) e

setTypeOfFreeInLet :: TypedVar -> [GenBnd] -> GenExpr -> ([GenBnd],GenExpr)
setTypeOfFreeInLet tv [] bdy = ([],setTypeOfFree tv bdy)
setTypeOfFreeInLet tv (b@(CS.Binding ip m e bvs) : bs) bdy =
    ((CS.Binding ip' m e' bvs) : bs'', bdy'')
    where e' = setTypeOfFree tv e
          otv = if elem (namOfTV tv) (freeInIrrefPatn ip) then [] else [tv]
          (ip',bmvs) = fixTypeOfBound ip (typOfGE e) (typOfGE e')
          (bs'',bdy'') = setTypeOfVarsInLet (union otv bmvs) bs bdy

setTypeOfVarsInLet :: [TypedVar] -> [GenBnd] -> GenExpr -> ([GenBnd],GenExpr)
setTypeOfVarsInLet [] bs bdy = (bs,bdy)
setTypeOfVarsInLet (tv : tvs) bs bdy =
    setTypeOfVarsInLet tvs bs' bdy'
    where (bs',bdy') = setTypeOfFreeInLet tv bs bdy

-- | Fix type of variables according to type changes in an expression.
-- The result is the fixed pattern and the list of all fixed variables with their new types.
-- The second argument is the old type, the third is the new type of the bound expression.
fixTypeOfBound :: GenIrrefPatn -> GenType -> GenType -> (GenIrrefPatn,[TypedVar])
fixTypeOfBound (GenIrrefPatn (CS.PTuple ips) o _) (GenType (CS.TTuple ts1) _ _) (GenType (CS.TTuple ts2) _ _) =
    (GenIrrefPatn (CS.PTuple ips') o (mkTupleType $ map typOfGIP ips'), nub $ concat tvss)
    where (ips',tvss) = unzip $ map (\(ip,t1,t2) -> fixTypeOfBound ip t1 t2) $ zip3 ips ts1 ts2
fixTypeOfBound (GenIrrefPatn (CS.PVar pv) o _) t1 t2 | isMayNull t1 /= isMayNull t2 =
    (GenIrrefPatn (CS.PVar pv) o t2, [TV pv t2])
fixTypeOfBound (GenIrrefPatn (CS.PTake pv tfs) o _) t1 t2 | isMayNull t1 /= isMayNull t2 =
    (GenIrrefPatn (CS.PTake pv tfs) o t2, [TV pv t2])
fixTypeOfBound (GenIrrefPatn (CS.PArrayTake pv tfs) o _) t1 t2 | isMayNull t1 /= isMayNull t2 =
    (GenIrrefPatn (CS.PArrayTake pv tfs) o t2, [TV pv t2])
fixTypeOfBound ip _ _ = (ip,[])

-- | Resolve type incompatibilities between MayNull wrapped types and unwrapped types.
-- Unwrapped types in MayNull context are converted by mayNull.
-- MayNull types in unwrapped context are signaled as error and resolved by dummy expressions.
-- The type of the expression remains unchanged.
rslvMayNullDiffs :: GenExpr -> ETrav GenExpr
rslvMayNullDiffs = resolveExpr convVarMayNullDiffs

convVarMayNullDiffs :: ConvVarFun
convVarMayNullDiffs (GenExpr _ _ t1 _) t2 | isMayNull t1 == isMayNull t2 = return Nothing
convVarMayNullDiffs e@(GenExpr (CS.Var v) o t1 _) t2 | isMayNull t1 = do
    recordError $ typeMatch o msg
    return $ Just $ mkVarBinding (TV v t2) $ toDummyExpr e $ mkDummyExpr t2 msg
    where msg = "MayNull expression used in not-null context"
convVarMayNullDiffs e@(GenExpr (CS.Var v) o t1 _) t2 | isMayNull t2 =
    return $ Just $ mkVarBinding (TV v t2)
         $ mkAppExpr (mkTopLevelFunExpr ("mayNull",mkFunType t1 t2) [Just t1]) e
convVarMayNullDiffs _ _ = return Nothing


{- Generic resolving of type clashes        -}
{- using conversion function applications.  -}
{--------------------------------------------}

-- | Conversion generation function type.
-- This kind of function implements conversion generation for a specific set of types.
-- The first argument must be an expression for a single variable.
-- If the function supports conversion from the variable type to the second type by applying a conversion function cf
-- it returns a binding v = cf v where v is the variable specified as first argument.
-- If a conversion from the variable type to the second type is impossible
-- it returns a binding v = gencotDummy(...) and signals an error.
-- If it does not handle the variable type it returns Nothing.
type ConvVarFun = GenExpr -> GenType -> ETrav (Maybe GenBnd)

umkSafeLetExpr = liftM (uncurry mkSafeLetExpr)

-- | Resolve all type clashes in an expression which can be converted by the given conversion generation function.
resolveExpr :: ConvVarFun -> GenExpr -> ETrav GenExpr
resolveExpr cv (GenExpr (CS.Let bs bdy) o t ccd) = do
    (bs', bdy') <- resolveExprInLet cv bs bdy
    return $ GenExpr (CS.Let bs' bdy') o t ccd
resolveExpr cv (GenExpr (CS.If e0 bvs e1 e2) o t ccd) = do
    e0' <- resolveExpr cv e0
    e1' <- convBranch cv t =<< resolveExpr cv e1
    e2' <- convBranch cv t =<< resolveExpr cv e2
    umkSafeLetExpr $ rslvExpr cv $ GenExpr (CS.If e0' bvs e1' e2') o t ccd
resolveExpr cv (GenExpr (CS.Match e bvs alts) o t ccd) = do
    e' <- resolveExpr cv e
    alts' <- mapM (\(CS.Alt p l ae) -> (liftM (CS.Alt p l)) $ convBranch cv t =<< resolveExpr cv ae) alts
    return $ GenExpr (CS.Match e' bvs alts') o t ccd
resolveExpr cv e = mapMExprOfGE (mapM (resolveExpr cv)) e

resolveExprInLet :: ConvVarFun -> [GenBnd] -> GenExpr -> ETrav ([GenBnd],GenExpr)
resolveExprInLet cv [] bdy = do
    bdy' <- resolveExpr cv bdy
    case exprOfGE bdy' of
         CS.Let bs bdy'' -> return (bs,bdy'')
         _ -> return ([],bdy')
resolveExprInLet cv (b@(CS.Binding ip m e bvs):bs) bdy = do
    (cbs,e') <- rslvExpr cv =<< resolveExpr cv e
    (cbs1,cbs2,ip') <- rslvBnd cv b
    (bs',bdy') <- resolveExprInLet cv bs bdy
    return (cbs ++ cbs1 ++ [CS.Binding ip' m e' bvs] ++ cbs2 ++ bs', bdy')

-- | Try to convert a branch in an If or Match expression to a given type.
convBranch :: ConvVarFun -> GenType -> GenExpr -> ETrav GenExpr
convBranch cv t e@(GenExpr (CS.Tuple _) _ _ _) = umkSafeLetExpr $ convVars cv t e
convBranch cv t e@(GenExpr (CS.Var _) _ _ _) = umkSafeLetExpr $ convVars cv t e
convBranch cv t (GenExpr (CS.Let bs bdy) o _ ccd) = do
    (cbs,bdy') <- (liftM extractBindingsFromLet) $ convBranch cv t bdy
    return $ GenExpr (CS.Let (bs ++ cbs) bdy') o (typOfGE bdy') ccd
convBranch cv t (GenExpr (CS.If e0 bvs e1 e2) o _ ccd) = do
    e1' <- convBranch cv t e1
    e2' <- convBranch cv t e2
    return $ GenExpr (CS.If e0 bvs e1' e2') o (adaptTypes (typOfGE e1') (typOfGE e2')) ccd
convBranch cv t (GenExpr (CS.Match e bvs alts) o _ ccd) = do
    alts' <- mapM (\(CS.Alt p l e) -> (liftM (CS.Alt p l)) $ convBranch cv t e) alts
    let tm = foldl1' adaptTypes $ map (\(CS.Alt _ _ e) -> typOfGE e) alts'
    return $ GenExpr (CS.Match e bvs alts') o tm ccd
convBranch cv t e = return e -- should not occur.

extractBindingsFromLet :: GenExpr -> ([GenBnd], GenExpr)
extractBindingsFromLet (GenExpr (CS.Let bs bdy) _ _ _) = (bs,bdy)
extractBindingsFromLet e = ([],e)

rslvExpr :: ConvVarFun -> GenExpr -> ETrav ([GenBnd],GenExpr)
rslvExpr cv (GenExpr (CS.App f e i) o te ccd) = do
    (cbs,e') <- convVars cv (getParamType $ typOfGE f) e
    return (cbs, GenExpr (CS.App f e' i) o te ccd)
rslvExpr cv (GenExpr (CS.PrimOp op es) o te ccd) = do
    (cbss,es') <- (liftM unzip) $ mapM (convVars cv t') es
    return (concat cbss, GenExpr (CS.PrimOp op es') o te ccd)
    where t' = getOpArgType op te es
rslvExpr cv e@(GenExpr (CS.If e0 bvs e1 e2) o te ccd) = do
    (cbs,e0') <- convVars cv mkBoolType e0
    return (cbs,GenExpr (CS.If e0' bvs e1 e2) o te ccd)
rslvExpr cv e@(GenExpr (CS.ArrayPut pv [(idx, el)]) o te ccd) =
    if isArithmetic $ typOfGE idx
       then return ([],e)
       else do
           mb <- cv idx mkU32Type
           case mb of
                Just b -> return ([], -- no conversion binding, the same value variable has already been converted for the take.
                                  GenExpr (CS.ArrayPut pv [(mapTypeOfGE (const mkU32Type) idx, el)]) o te ccd)
                Nothing -> return ([],e)
rslvExpr cv e = return ([],e)

getOpArgType :: CCS.OpName -> GenType -> [GenExpr] -> GenType
getOpArgType op rt es | elem op ["==", "/="] =
    adaptTypes (typOfGE $ head es) (typOfGE $ head $ tail es)
getOpArgType op rt es | elem op ["<", ">", "<=", ">="] =
    if at1 && at2
       then adaptTypes t1 t2
       else if at1 then t1
       else if at2 then t2
       else mkU32Type
    where t1 = typOfGE $ head es
          t2 = typOfGE $ head $ tail es
          at1 = isArithmetic t1
          at2 = isArithmetic t2
getOpArgType op rt es | op == "not" = mkBoolType
getOpArgType op rt es = rt

rslvBnd :: ConvVarFun -> GenBnd -> ETrav ([GenBnd],[GenBnd],GenIrrefPatn)
rslvBnd cv (CS.Binding ip@(GenIrrefPatn (CS.PVar pv) o t) m e bvs) = do
    (cbs,ip') <- rslvBndVar cv ip $ typOfGE e
    return ([],cbs,ip')
rslvBnd cv (CS.Binding (GenIrrefPatn (CS.PTuple ips) o t) m e bvs) | (CS.TTuple ts) <- typeOfGT $ typOfGE e = do
    (cbss,ips') <- (liftM unzip) $ mapM (uncurry $ rslvBndVar cv) $ zip ips ts
    return ([],concat cbss,GenIrrefPatn (CS.PTuple ips') o $ mkTupleType $ map typOfGIP ips')
rslvBnd cv (CS.Binding ip@(GenIrrefPatn (CS.PArrayTake pv [(idx, elp)]) o t) m e bvs) =
    if isArithmetic $ typOfGE idx
       then return ([],[],ip)
       else do
           mb <- cv idx mkU32Type
           case mb of
                Just b -> return ([b], [], GenIrrefPatn (CS.PArrayTake pv [(mapTypeOfGE (const mkU32Type) idx, elp)]) o t)
                Nothing -> return ([],[],ip)
rslvBnd cv (CS.Binding ip m e bvs) = return ([],[],ip)

rslvBndVar :: ConvVarFun -> GenIrrefPatn -> GenType -> ETrav ([GenBnd], GenIrrefPatn)
rslvBndVar cv ip@(GenIrrefPatn (CS.PVar pv) ov tv) t = do
    mb <- cv (mkVarExpr $ TV pv t) tv
    case mb of
         Just b -> return ([b],GenIrrefPatn (CS.PVar pv) ov t)
         Nothing -> return ([],ip)
rslvBndVar _ ip _ = return ([],ip)

convVars :: ConvVarFun -> GenType -> GenExpr -> ETrav ([GenBnd], GenExpr)
convVars cv t e@(GenExpr (CS.Var _) _ _ _) = do
    mb <- cv e t
    case mb of
         Just b -> return ([b],mapTypeOfGE (const t) e)
         Nothing -> return ([],e)
convVars cv t e@(GenExpr (CS.Tuple es) o _ ccd) | (CS.TTuple ts) <- typeOfGT t = do
    (bss,es') <- (liftM unzip) $ mapM (\(e,t) -> convVars cv t e) $ zip es ts
    return (concat bss, GenExpr (CS.Tuple es') o (mkTupleType $ map typOfGE es') ccd)
convVars cv t e = return ([],e)
