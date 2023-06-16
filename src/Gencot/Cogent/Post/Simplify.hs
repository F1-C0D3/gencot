{-# LANGUAGE PackageImports #-}
module Gencot.Cogent.Post.Simplify where

import Data.List (concatMap,nub,intersect,union,(\\),partition,find)
import qualified Data.Map as M
import Data.Maybe (catMaybes,isNothing,fromJust)
import Data.Foldable (toList)

import Cogent.Surface as CS
import Cogent.Common.Syntax as CCS

import Gencot.Cogent.Ast
import Gencot.Cogent.Types (mkTupleType)
import Gencot.Cogent.Expr (mkUnitExpr)
import Gencot.Cogent.Post.Util (isLiteralExpr,freeInPatn,freeInIrrefPatn,freeInExpr',freeInExpr,freeUnderBinding,boundInBindings)

{- Pre Simplification:        -}
{- Eliminate unused variables -}
{------------------------------}

presimp :: GenExpr -> GenExpr
presimp e =
    case exprOfGE e of
         (Let bs bdy) ->
            let bdy' = presimp bdy
                xbdy' = exprOfGE bdy'
                bs' = presimpBinds bs xbdy'
            in if null bs'
                  then mapExprOfGE (const xbdy') e
                  else mapExprOfGE (const (Let bs' $ mapExprOfGE (const xbdy') bdy)) e
         _ -> mapExprOfGE (fmap presimp) e

-- | Process all bindings in a binding sequence by removing unused bound variables.
-- The second argument is an expression where the variables may be used.
-- The bindings in the sequence are processed from the last one backwards.
presimpBinds :: [GenBnd] -> ExprOfGE -> [GenBnd]
presimpBinds [] bdy = []
presimpBinds ((Binding ip Nothing e []) : bs) bdy =
    let bs' = presimpBinds bs bdy
    in case presimpBind ip e $ freeUnderBinding bs' bdy of
            Just (ip', e') -> ((Binding ip' Nothing (presimp e') []) : bs')
            _ -> bs'

-- | Process the binding (ip = e) by removing bindings to variables not in a given set.
-- If all components can be removed the result is Nothing
presimpBind :: GenIrrefPatn -> GenExpr -> [VarName] -> Maybe (GenIrrefPatn,GenExpr)
presimpBind ip@(GenIrrefPatn (PVar pv) _ _) e vs =
    if elem pv vs then Just (ip,e) else Nothing
presimpBind ip@(GenIrrefPatn (PTake pv [Just (_, GenIrrefPatn (PVar cv) _ _)]) _ _) e vs =
    if elem pv vs || elem cv vs then Just (ip,e) else Nothing
presimpBind ip@(GenIrrefPatn (PArrayTake pv [(_, GenIrrefPatn (PVar cv) _ _)]) _ _) e vs =
    if elem pv vs || elem cv vs then Just (ip,e) else Nothing
presimpBind ip@(GenIrrefPatn PUnitel _ _) e vs = Nothing
presimpBind ip@(GenIrrefPatn PUnderscore _ _) e vs = Nothing
presimpBind ip@(GenIrrefPatn (PTuple ips) op tp) (GenExpr (Let ebs ebdy) oe te ce) vs =
    case presimpBind ip ebdy vs of
         Just (ip', ebdy') -> Just (ip', GenExpr (Let ebs ebdy') oe (typOfGE ebdy') ce)
         _ -> Nothing
presimpBind ip@(GenIrrefPatn (PTuple ips) op tp) (GenExpr (If e0 [] e1 e2) oe te ce) vs =
    case presimpBind ip e1 vs of
         Just (ip', e1') ->
            let Just (_, e2') = presimpBind ip e2 vs
            in Just (ip', GenExpr (If e0 [] e1' e2') oe (typOfGE e1') ce)
         _ -> Nothing
presimpBind (GenIrrefPatn (PTuple ips) op tp) (GenExpr (Tuple es) oe te ce) vs =
     let bs' = catMaybes $ map (\(ip,e) -> presimpBind ip e vs) $ zip ips es
     in if null bs'
           then Nothing
           else if null $ tail bs'
           then Just $ head bs'
           else let  (ips',es') = unzip bs'
                in Just $ (GenIrrefPatn (PTuple ips') op (mkTupleType $ map typOfGIP ips'),
                           GenExpr (Tuple es') oe (mkTupleType $ map typOfGE es') ce)
presimpBind ip@(GenIrrefPatn (PTuple ips) _ _) e@(GenExpr (App _ _ _) _ _ _) vs =
    if null $ catMaybes $ map (\cip -> presimpBind cip mkUnitExpr vs) ips -- all components of ip unused in vs
       then Nothing
       else Just (ip,e)

{- Simplifying let expressions -}
{-------------------------------}

-- | Simplify all contained let expressions.
letproc :: GenExpr -> GenExpr
letproc e =
    case exprOfGE e of
         (Let bs bdy) -> 
            let (bs', bdy') = bindsproc bs $ exprOfGE $ letproc bdy
            in if null bs'
                  then mapExprOfGE (const bdy') e
                  else mapExprOfGE (const (Let bs' $ mapExprOfGE (const bdy') bdy)) e
         _ -> mapExprOfGE (fmap letproc) e

-- | Process all bindings without banged variables in a let expression.
-- If there are several and-concatenated bindings, they are processed from the last one backwards.
bindsproc :: [GenBnd] -> ExprOfGE -> ([GenBnd],ExprOfGE)
bindsproc [] bdy = ([], bdy)
bindsproc ((Binding ip Nothing e []) : bs) bdy = 
    let (bs',bdy') = bindsproc bs bdy
    in bindproc ip (letproc e) bs' bdy'
bindsproc ((Binding ip Nothing e bvs) : bs) bdy =
    let (bs',bdy') = bindsproc bs bdy
    in ((Binding ip Nothing (letproc e) bvs): bs',bdy')
bindsproc (b : _) _ = error ("unexpected binding in letproc/bindsproc: " ++ (show b))

-- | Process the binding (ip = e) by substituting it in expression (let bs in bdy).
-- First all possible matches are searched and counted in the expression using findMatches.
-- Then matches which violate conditions for free variables (retainFree) or grow the 
-- expression too much (retainGrowth) are marked as retained.
-- The remaining matches are substituted using substMatches.
-- If there are retained matches they are added as prepended binding.
bindproc :: GenIrrefPatn -> GenExpr -> [GenBnd] -> ExprOfGE -> ([GenBnd], ExprOfGE)
bindproc ip e bs bdy = 
    if M.null retain
       then (bs',bdy') 
       else ((Binding ip' Nothing e' []): bs',bdy')
    where (retain,subst) = M.partition ((== (-1)) . fst) $ retainGrowth $ retainFree $ findMatches ip e bs bdy
          (bs',bdy') = substMatches subst bs bdy
          -- instead of building the retained binding from the map 
          -- we reduce the original binding to the variables bound in the map
          (ip',e') = reduceBinding (boundInMap retain) ip e

type MatchMap = M.Map GenIrrefPatn (Int,GenExpr)

-- | Substitute matches from the map in an expression.
-- The expression corresponds to (let bs in bdy).
-- The result is the same expression with substituted matches, as a pair of the bindings and the body expression.
-- The map contains only matches which can be substituted in the expression.
substMatches :: MatchMap -> [GenBnd] -> ExprOfGE -> ([GenBnd],ExprOfGE)
substMatches m bs bdy | null m = (bs,bdy)
substMatches m [] bdy = ([],substMatchesE m bdy)
substMatches m ((Binding ipp Nothing ep []) : bs) bdy =
    (Binding ipp'' Nothing ep'' [] : bs',bdy')
    where (_,ep') = substMatches m [] $ exprOfGE ep
          ep'' = mapExprOfGE (const ep') ep
          ipp' = substMatchesIP m $ irpatnOfGIP ipp
          ipp'' = mapIrpatnOfGIP (const ipp') ipp
          m' = removeMatches (freeInIrrefPatn ipp) m
          (bs',bdy') = substMatches m' bs bdy

substMatchesE :: MatchMap -> ExprOfGE -> ExprOfGE
substMatchesE m (Let bs bdy) = Let bs' $ mapExprOfGE (const bdy') bdy
    where (bs',bdy') = substMatches m bs $ exprOfGE bdy
substMatchesE m (Match e vs alts) = 
    Match (mapExprOfGE (substMatchesE m) e) vs $ map (substMatchesA m) alts
substMatchesE m (Lam ip mt bdy) = 
    Lam ip mt $ mapExprOfGE (substMatchesE (removeMatches (freeInIrrefPatn ip) m)) bdy
substMatchesE m e =
    case find (((flip matches) e) . irpatnOfGIP . fst) $ M.assocs m of
         Nothing -> fmap (mapExprOfGE (substMatchesE m)) e
         Just (_,(_,e')) -> exprOfGE e'

substMatchesA :: MatchMap -> GenAlt -> GenAlt
substMatchesA m (Alt p l bdy) = 
    Alt p l $ mapExprOfGE (substMatchesE (removeMatches (freeInPatn p) m)) bdy

substMatchesIP :: MatchMap -> IrpatnOfGIP -> IrpatnOfGIP
substMatchesIP m (PArrayTake pv [(e,ip)]) =
    PArrayTake pv [(mapExprOfGE (substMatchesE m) e,ip)]
substMatchesIP m (PTuple ips) = PTuple $ map (mapIrpatnOfGIP (substMatchesIP m)) ips
substMatchesIP _ ip = ip

-- | Retain bindings for which the substitution would grow the expression too much.
-- Not yet implemented.
-- (TODO)
retainGrowth :: MatchMap -> MatchMap
retainGrowth m = m

-- | Retain all bindings with free variables which are bound by retained bindings
retainFree :: MatchMap -> MatchMap
retainFree m = 
    if M.null freemap 
       then m
       else retainFree $ M.mapWithKey (\ip (i,e) -> if M.member ip freemap then (-1,e) else (i,e)) m
    where boundvars = nub $ concatMap freeInIrrefPatn $ M.keys $ M.filter ((== (-1)) . fst) m
          freemap = M.filter (\(i,e) -> i >= 0 && any (\v -> elem v boundvars) (freeInExpr e)) m

-- | Remove patterns with variables in the given set.
removeMatches :: [VarName] -> MatchMap -> MatchMap
removeMatches vs m =
    M.filterWithKey (\ip _ -> null $ intersect vs (freeInIrrefPatn ip)) m

-- | Find matches of a binding (ip = e) in the expression (let bs in bdy).
-- During matching the binding may be split by splitting the pattern and the corresponding expression.
-- The result is a map from subpatterns to subexpressions and the number of matches. 
-- If the number is -1 the subpattern cannot be substituted and must be retained in the original binding.
findMatches :: GenIrrefPatn -> GenExpr -> [GenBnd] -> ExprOfGE -> MatchMap
findMatches ip e bs@((Binding ipp Nothing ep []) : bs') bdy =
    if isUnitPattern ip'
       then M.empty
       else combineMatches [msp, msi, ms1, ms2]
    where (ip',e') = reduceBinding (freeUnderBinding bs bdy) ip e
          msp = findMatches ip' e' [] $ exprOfGE ep
          msi = findMatchesInIndex ip' e' $ irpatnOfGIP ipp
          ((ip1,e1),(ip2,e2)) = splitBinding (freeInIrrefPatn ipp) ip' e'
          ms1 = findMatches ip1 e1 bs' bdy
          ms2 = retainOrDrop $ findMatches ip2 e2 bs' bdy
findMatches _ _ (b : _) _ = error ("unexpected binding in letproc/findMatches: " ++ (show b))
findMatches ip e [] bdy = 
    if isUnitPattern ip'
       then M.empty
       else findFullMatches ip' e' bdy
    where (ip',e') = reduceBinding (freeInExpr' bdy) ip e

findMatchesInIndex :: GenIrrefPatn -> GenExpr -> IrpatnOfGIP -> MatchMap
findMatchesInIndex ip e (PArrayTake _ [(idx,_)]) =
    if isUnitPattern ip'
       then M.empty
       else findFullMatches ip' e' idx'
    where idx' = exprOfGE idx
          (ip',e') = reduceBinding (freeInExpr' idx') ip e
findMatchesInIndex ip e (PTuple ips) =
    combineMatches $ map (findMatchesInIndex ip e . irpatnOfGIP) ips
findMatchesInIndex _ _ _ = M.empty

-- | Find matches of a binding in an expression.
-- The binding binds only variables which occur free in the expression.
-- The binding binds at least one variable.
findFullMatches :: GenIrrefPatn -> GenExpr -> ExprOfGE -> MatchMap
findFullMatches ip e bdy@(Var _) = M.singleton ip (cnt,e)
    where cnt = if matches (irpatnOfGIP ip) bdy then 1 else -1
findFullMatches ip e bdy@(Tuple es) =
    if matches (irpatnOfGIP ip) bdy
       then M.singleton ip (1,e)
       else combineMatches $ map (findMatches ip e [] . exprOfGE) es
findFullMatches ip e (Let bs bdy) = findMatches ip e bs $ exprOfGE bdy
findFullMatches ip e (Match e' vs alts) =
    combineMatches [ms',ms]
    where ms' = findMatches ip e [] $ exprOfGE e'
          ms = combineMatches $ map (\(Alt p _ bdy) -> findMatchesUnderBoundVars ip e (freeInPatn p) $ exprOfGE bdy) alts
findFullMatches ip e (Lam ip' mt bdy) = M.empty -- Cogent supports no closures, no free variables allowed in lambda expression
findFullMatches ip e bdy =
    combineMatches $ map (findMatches ip e [] . exprOfGE) $ toList bdy

findMatchesUnderBoundVars :: GenIrrefPatn -> GenExpr -> [VarName] -> ExprOfGE -> MatchMap
findMatchesUnderBoundVars ip e vs bdy = 
    combineMatches [ms1, ms2]
    where ((ip1,e1),(ip2,e2)) = splitBinding vs ip e
          ms1 = findMatches ip1 e1 [] bdy
          ms2 = retainOrDrop $ findMatches ip2 e2 [] bdy

-- | Match a pattern with an expression.
-- Currently only successful for nested variable tuple patterns.
-- This means that other patterns are never substituted by simplifying let expressions.
matches :: IrpatnOfGIP -> ExprOfGE -> Bool
matches (PVar v) (Var v') = v == v'
matches (PTuple ips) (Tuple es) = 
    (length ips) == (length es) && 
    (all (uncurry matches) $ zip (map irpatnOfGIP ips) (map exprOfGE es))
matches _ _ = False


-- | Variables bound in the patterns of a MatchMap.
boundInMap :: MatchMap -> [VarName]
boundInMap m = nub $ concatMap freeInIrrefPatn $ M.keys m

-- | Reduce the binding (ip = e) to a set of variables.
-- All variables bound in the pattern which are not in the set are replaced by a wildcard.
-- Then all wildcards are removed from the pattern for which the corrsponding part 
-- can be removed from the expression.
reduceBinding :: [VarName] -> GenIrrefPatn -> GenExpr -> (GenIrrefPatn,GenExpr)
reduceBinding vs ip e =
    if null ivars
       then toUnitBinding ip e
       else if null uvars
               then removeWildcards ip e
               else removeWildcards (mapIrpatnOfGIP (replaceVarsInPattern uvars) ip) e
    where 
        pvars = freeInIrrefPatn ip
        ivars = intersect vs pvars
        uvars = pvars \\ ivars

toUnitBinding :: GenIrrefPatn -> GenExpr -> (GenIrrefPatn,GenExpr)
toUnitBinding ip e = (mapIrpatnOfGIP (const PUnitel) ip, mapExprOfGE (const Unitel) e)

isUnitPattern :: GenIrrefPatn -> Bool
isUnitPattern ip = (irpatnOfGIP ip) == PUnitel

-- | Replace occurrences of variables in a pattern by the wildcard pattern.
-- Variables bound to the container in a take pattern are not replaced, since that would drop the container.
replaceVarsInPattern :: [VarName] -> IrpatnOfGIP -> IrpatnOfGIP
replaceVarsInPattern vs ip@(PVar v) = 
    if elem v vs then PUnderscore else ip
replaceVarsInPattern vs (PTuple ips) =
    PTuple $ map (mapIrpatnOfGIP (replaceVarsInPattern vs)) ips
replaceVarsInPattern vs (PUnboxedRecord flds) =
    PUnboxedRecord $ map (fmap (\(n,ip) -> (n,mapIrpatnOfGIP (replaceVarsInPattern vs) ip))) flds
replaceVarsInPattern vs PUnderscore = PUnderscore
replaceVarsInPattern vs PUnitel = PUnitel
replaceVarsInPattern vs (PTake v flds) = 
    PTake v $ map (fmap (\(n,ip) -> (n,mapIrpatnOfGIP (replaceVarsInPattern vs) ip))) flds
replaceVarsInPattern vs (PArray ips) = 
    PArray $ map (mapIrpatnOfGIP (replaceVarsInPattern vs)) ips
replaceVarsInPattern vs (PArrayTake v els) =
    PArrayTake v $ map (\(e,ip) -> (e,mapIrpatnOfGIP (replaceVarsInPattern vs) ip)) els

-- | Remove as much wildcards as possible from a pattern and remove the corresponding parts from a matching expression.
-- If the pattern only contains wildcards (i.e. binds no variable) it is replaced by a unit pattern.
removeWildcards :: GenIrrefPatn -> GenExpr -> (GenIrrefPatn,GenExpr)
removeWildcards ip e = 
    if not $ containsWildcard ip
       then (ip,e)
       else if onlyWildcards ip
              then toUnitBinding ip e
              else case irpatnOfGIP ip of
                        -- must be structured since it contains wildcards and non-wildcards
                        PTuple ips -> removeWildcardsFromTuple ip ips e
                        -- we do not split records or arrays
                        _ -> (ip,e)
    where removeWildcardsFromTuple ip ips e = 
            case exprOfGE e of
                 Tuple es -> 
                   let bs = map (uncurry removeWildcards) $ zip ips es
                   in toTupleBind (filter (not . isUnitPattern . fst) bs) ip e
                 If c vs et ee -> 
                   let (ipt,et') = removeWildcards ip et
                       (ipe,ee') = removeWildcards ip ee
                       e' = mapExprOfGE (const (If c vs et' ee')) e
                   in if ip == ipt || ipt /= ipe
                         then (ip, e)
                         else (ipt, e')
                 Let bs bdy ->
                   let (ip',bdy') = removeWildcards ip bdy
                       e' = mapExprOfGE (const (Let bs bdy')) e
                   in if ip == ip' 
                         then (ip,e)
                         else (ip', letproc e')
                 -- todo: Match, Lam
                 _ -> (ip,e)

-- | Test whether a pattern contains a wildcard.
containsWildcard :: GenIrrefPatn -> Bool
containsWildcard ip = 
    case irpatnOfGIP ip of 
         PUnderscore -> True
         PVar _ -> False
         PUnitel -> False
         PTuple ips -> any containsWildcard ips
         PUnboxedRecord flds -> any (containsWildcard . snd) (catMaybes flds)
         PTake v flds -> any (containsWildcard . snd) (catMaybes flds)
         PArray ips -> any containsWildcard ips
         PArrayTake v els -> any (containsWildcard . snd) els

-- | Test whether a pattern only consists of wildcards.
onlyWildcards :: GenIrrefPatn -> Bool
onlyWildcards ip =
    case irpatnOfGIP ip of 
         PUnderscore -> True
         PVar _ -> False
         PUnitel -> False
         PTuple ips -> all onlyWildcards ips
         PUnboxedRecord flds -> all (onlyWildcards . snd) (catMaybes flds)
         PTake v flds -> False -- since it contains v
         PArray ips -> all onlyWildcards ips
         PArrayTake v els -> False -- since it contains v

-- | Turn a sequence of bindings into a tuple binding.
-- If the sequence has length 0, the result is a unit binding.
-- If the sequence has length 1, its single binding is returned.
-- Otherwise the result reuses a given pattern and expression.
toTupleBind :: [(GenIrrefPatn,GenExpr)] -> GenIrrefPatn -> GenExpr -> (GenIrrefPatn,GenExpr)
toTupleBind bs ip e = 
    if null bs
       then toUnitBinding ip e
       else if (length bs) == 1
               then head bs
               else let ubs = unzip bs
                    in (mapIrpatnOfGIP (const (PTuple (fst ubs))) ip,
                        mapExprOfGE (const (Tuple (snd ubs))) e)

-- | Split the binding (ip = e) according to a set of variables.
-- The binding is split into a maximal part where no variable in the set 
-- occurs free in the expression and the rest part. If one of these parts is empty the corresponding 
-- pattern is the unit pattern.
splitBinding :: [VarName] -> GenIrrefPatn -> GenExpr -> ((GenIrrefPatn,GenExpr),(GenIrrefPatn,GenExpr))
splitBinding vs ip e = (reduceBinding nfbvs ip e,reduceBinding fbvs ip e)
    where fbvs = boundVarsToRetain vs ip e
          nfbvs = (freeInIrrefPatn ip) \\ fbvs
          
-- | Determine all variables bound in ip where the corresponding parts of e contains
-- a free occurrence of a variable in vs.
boundVarsToRetain :: [VarName] -> GenIrrefPatn -> GenExpr -> [VarName]
boundVarsToRetain vs ip e =
    if null (intersect vs $ freeInExpr e)
       then []
       else case irpatnOfGIP ip of
                 PTuple ips -> 
                   case exprOfGE e of
                        Tuple es -> nub $ concatMap (uncurry (boundVarsToRetain vs)) $ zip ips es
                        If c _ et ee -> union (boundVarsToRetain vs ip et) (boundVarsToRetain vs ip ee)
                        Let bs bdy -> boundVarsToRetain (vs \\ boundInBindings bs) ip bdy
                        -- todo: Match, Lam
                        _ -> allVars
                 _ -> allVars
    where allVars = (freeInIrrefPatn ip)

-- | Combine match results.
-- If a pattern occurs in both maps the expressions are the same. The number of matches is -1 if 
-- it is -1 in either map, otherwise the sum of the matches in both maps.
combineMatches :: [MatchMap] -> MatchMap
combineMatches = 
    M.unionsWith (\(i1,e1) (i2,e2) -> (if i1 == -1 || i2 == -1 then -1 else i1+i2, e1))

-- | Drop sub bindings with 0 matches and retain all others (set matches to -1)
retainOrDrop :: MatchMap -> MatchMap
retainOrDrop m = 
    M.map (\(_,e) -> (-1,e)) $ M.filter (\(i,_) -> i /= 0) m

{- Evaluating constant expressions -}
{-----------------------------------}

-- | Evaluate constant parts of operator application. 
-- Arguments are only processed if they are constant or again operator applications.
-- Bitwise operators are not processed.
evalproc :: GenExpr -> GenExpr
evalproc e =
    case exprOfGE e of
         (PrimOp op args) ->
           let args' = map evalproc args
           in if all (isLiteralExpr . exprOfGE) args'
                then toEval op args' e
                else mapExprOfGE (const (PrimOp op args')) e
         _ -> e

toEval :: OpName -> [GenExpr] -> GenExpr -> GenExpr
toEval op args e | op `elem` ["==", "/="] =
    let res = if op == "==" 
                 then (head args) == (head $ tail args)
                 else (head args) /= (head $ tail args)
    in mapExprOfGE (const (BoolLit res)) e
toEval op args e | op `elem` [">=", "<=", "<", ">"] =
    case exprOfGE $ head args of
         i1@(IntLit _) -> mapExprOfGE (const (BoolLit $ evalIntPred op i1 $ exprOfGE $ head $ tail args)) e
         _ -> e
toEval op args e | op `elem` ["&&", "||"] =
    case exprOfGE $ head args of
         b1@(BoolLit _) -> mapExprOfGE (const (BoolLit $ evalBoolOp op b1 $ exprOfGE $ head $ tail args)) e
         _ -> e
toEval op args e | op `elem` ["-"] && (length args) == 1 =
    case exprOfGE $ head args of
         IntLit i -> mapExprOfGE (const (IntLit (- i))) e
         _ -> e
toEval op args e | op `elem` ["+", "-", "*", "/", "%"] =
    case exprOfGE $ head args of
         i1@(IntLit _) -> mapExprOfGE (const (IntLit $ evalIntOp op i1 $ exprOfGE $ head $ tail args)) e
         _ -> e
toEval op args e | op `elem` ["not"] =
    case exprOfGE $ head args of
         BoolLit b -> mapExprOfGE (const (BoolLit (not b))) e
         _ -> e

evalIntPred :: OpName -> ExprOfGE -> ExprOfGE -> Bool
evalIntPred op (IntLit i1) (IntLit i2) = 
    case op of
         ">=" -> i1 >= i2
         "<=" -> i1 <= i2
         "<"  -> i1 <  i2
         ">"  -> i1 >  i2
evalIntOp :: OpName -> ExprOfGE -> ExprOfGE -> Integer
evalIntOp op (IntLit i1) (IntLit i2) = 
    case op of
         "+" -> i1 + i2
         "-" -> i1 - i2
         "*" -> i1 * i2
         "/" -> i1 `div` i2
         "%" -> i1 `mod` i2

evalBoolOp :: OpName -> ExprOfGE -> ExprOfGE -> Bool
evalBoolOp op (BoolLit b1) (BoolLit b2) = 
    case op of
         "&&" -> b1 && b2
         "||" -> b1 || b2

{- Simplifying if expressions -}
{------------------------------}

-- | Simplify all contained conditional expressions.
-- For a conditional expression, if the condition can be statically evaluated, the expression
-- is replaced by one of the branches. Then other rules are applied.
-- For an operation where the first argument is a conditional expression and the second can be 
-- statically evaluated, the operation is drawn into the branches.
ifproc :: GenExpr -> GenExpr
ifproc e =
    case exprOfGE e of
         If c vs e1 e2 -> 
           let c' = evalproc $ ifproc c
               e1' = ifproc e1
               e2' = ifproc e2
           in case exprOfGE c' of
                   BoolLit True -> e1'
                   BoolLit False -> e2'
                   _ -> mapExprOfGE (const (ifrules usedRules $ If c' vs e1' e2')) e
         PrimOp op (arg1 : (arg2 : [])) ->
           let arg2' = evalproc arg2
           in case exprOfGE arg1 of
                   If c vs e1 e2 ->
                     if isLiteralExpr $ exprOfGE arg2'
                        then let e1' = mapExprOfGE (const (PrimOp op [e1, arg2'])) e1
                                 e2' = mapExprOfGE (const (PrimOp op [e2, arg2'])) e2
                             in ifproc $ mapExprOfGE (const (If c vs e1' e2')) e
                        else rec
                   _ -> rec
         _ -> rec
    where rec = mapExprOfGE (fmap ifproc) e

type IfRule = ExprOfGE -> Either ExprOfGE ExprOfGE 

-- The rules applied to conditional expressions, tried from left to right.
usedRules = [sameBranches, boolBranches, substCondition]

-- | Apply a sequence of rules to a conditional expression.
-- If a rule returns Left, stop the application of further rules, otherwise go on.
ifrules :: [IfRule] -> ExprOfGE -> ExprOfGE
ifrules [] e = e
ifrules (rl : rls) e =
    case rl e of
         Left e' -> e'
         Right e' -> ifrules rls e'

-- | If both branches are the same, replace expression by branch.
sameBranches :: IfRule
sameBranches (If c vs e1 e2) = 
    let e1' = evalproc e1
        e2' = evalproc e2
    in if toRawExpr e1' == toRawExpr e2'
          then Left $ exprOfGE e1'
          else Right $ If c vs e1' e2'

-- | If both branches can be statically evaluated to a boolean value, 
-- replace expression by condition or negated condition.
boolBranches :: IfRule
boolBranches e@(If c vs e1 e2) =
    case exprOfGE e1 of
         BoolLit b1 ->
           case exprOfGE e2 of 
                BoolLit b2 ->
                  if b1 && not b2 
                     then Left $ exprOfGE c
                     else if not b1 && b2
                             then Left $ PrimOp "not" [c]
                             else Right e
                _ -> Right e
         _ -> Right e

-- | Substitute the condition by True in the first branch and by False in the second branch.
substCondition :: IfRule
substCondition e@(If c vs e1 e2) =
    let e1' = substCond (toRawExpr c) (BoolLit True) e1
        e2' = substCond (toRawExpr c) (BoolLit False) e2
    in Right $ If c vs e1' e2'

substCond :: RawExpr -> ExprOfGE -> GenExpr -> GenExpr
substCond c b e =
    if c == toRawExpr e
       then mapExprOfGE (const b) e
       else case substAssoc "" (unRE c) b e of
                 Just e' -> mapExprOfGE (const e') e
                 Nothing -> mapExprOfGE (fmap (substCond c b)) e

substAssoc "" (PrimOp op (arg1 : (arg2 : []))) b e | op `elem` ["&&","||"] =
    case exprOfGE e of
         PrimOp op' (e1 : (e2 : [])) | op == op' && arg1 == toRawExpr e1 ->
           substAssoc op (unRE arg2) b e2
         _ -> Nothing
substAssoc ope (PrimOp op (arg1 : (arg2 : []))) b e | op == ope =
    case exprOfGE e of
         PrimOp op' (e1 : (e2 : [])) | op == op' && arg1 == toRawExpr e1 ->
           substAssoc ope (unRE arg2) b e2
         _ -> Nothing
substAssoc ope c b e =
    case exprOfGE e of
         PrimOp op (e1 : (e2 : [])) | op == ope && c == (unRE $ toRawExpr e1) ->
           Just $ PrimOp op [mapExprOfGE (const b) e1,e2]
         _ -> Nothing

{- Simplifying operator expressions -}
{------------------------------------}

-- | Simplify all contained operator applications.
-- Currently, only boolean operations are simplified, if the first argument
-- can be statically evaluated.
opproc :: GenExpr -> GenExpr
opproc e =
    case exprOfGE e of
         PrimOp "||" (e1 : (e2 : [])) ->
           case exprOfGE e1 of
                (BoolLit False) -> opproc e2
                (BoolLit True)  -> e1
                _ -> rec
         PrimOp "&&" (e1 : (e2 : [])) ->
           case exprOfGE e1 of
                (BoolLit False) -> e1
                (BoolLit True)  -> opproc e2
                _ -> rec
         _ -> rec
    where rec = mapExprOfGE (fmap opproc) e
