{-# LANGUAGE PackageImports #-}
module Gencot.Cogent.Simplify where

import Data.List (concatMap,nub,intersect,(\\),partition,find)
import qualified Data.Map as M
import Data.Maybe (catMaybes,isNothing,fromJust)
import Data.Foldable (toList)

import Cogent.Surface as CS
import Cogent.Common.Syntax as CCS

import Gencot.Cogent.Ast
 
letproc :: GenExpr -> GenExpr
letproc (GenExpr (CS.Let bs e) o src) = GenExpr (bindsproc (reverse bs) [] (letproc e)) o src
letproc (GenExpr e o src) = GenExpr (fmap letproc e) o src

bindsproc :: [GenBnd] -> [GenBnd] -> GenExpr -> ExprOfGE
bindsproc [] [] e = exprOfGE e
bindsproc [] bsp e = CS.Let bsp e
bindsproc ((CS.Binding ip Nothing e []) : bs) bps bdy = bindproc ip e bs bps bdy
bindsproc (b : _) _ _ = error ("unexpected binding in letproc: " ++ (show b))

bindproc :: GenIrrefPatn -> GenExpr -> [GenBnd] -> [GenBnd] -> GenExpr -> ExprOfGE
bindproc ip e bs bps bdy = bindsproc bs bps'' bdy'
    where (retain,subst) = M.partition ((== (-1)) . fst) $ retainGrowth $ retainFree $ findMatches ip e bps bdy
          (bps',bdy') = substMatches subst bps bdy
          bps'' = if M.null retain 
                     then bps' 
                     else case reduceBinding (freeInMap retain) ip e of
                               Nothing -> error ("cannot build retain binding in letproc for " ++ (show ip))
                               Just (ip',e') -> (CS.Binding ip' Nothing e' []): bps'

type MatchMap = M.Map GenIrrefPatn (Int,GenExpr)

-- | Substitute matches from the map in an expression.
-- The expression corresponds to a let expression consisting of the bindings and the body expression.
-- The result is the same expression with substituted matches, as a pair of the bindings and the body expression.
-- The map contains only matches which can be substituted in the expression.
substMatches :: MatchMap -> [GenBnd] -> GenExpr -> ([GenBnd],GenExpr)
substMatches m ((CS.Binding ipp Nothing ep []) : bps) bdy =
    (CS.Binding ipp Nothing ep' [] : bps',bdy')
    where (_,ep') = substMatches m [] ep
          m' = removeMatches (freeInIrrefPatn ipp) m
          (bps',bdy') = substMatches m' bps bdy
substMatches m [] bdy = ([],mapExprOfGE (substMatchesE m) bdy)

substMatchesE :: MatchMap -> ExprOfGE -> ExprOfGE
substMatchesE m (CS.Let bs bdy) = CS.Let bs' bdy'
    where (bs',bdy') = substMatches m bs bdy
substMatchesE m (CS.Match e vs alts) = 
    CS.Match (mapExprOfGE (substMatchesE m) e) vs $ map (substMatchesA m) alts
substMatchesE m (CS.Lam ip mt bdy) = 
    CS.Lam ip mt $ mapExprOfGE (substMatchesE (removeMatches (freeInIrrefPatn ip) m)) bdy
substMatchesE m e =
    case find (((flip matches) e) . irpatnOfGIP . fst) $ M.assocs m of
         Nothing -> fmap (mapExprOfGE (substMatchesE m)) e
         Just (_,(_,e')) -> exprOfGE e'

substMatchesA :: MatchMap -> GenAlt -> GenAlt
substMatchesA m (CS.Alt p l bdy) = 
    CS.Alt p l $ mapExprOfGE (substMatchesE (removeMatches (freeInPatn p) m)) bdy

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

-- | Find matches of a binding in an expression.
-- The expression corresponds to a let expression consisting of the bindings and the body expression.
-- The bindings have already been processed and have the expected form.
-- During matching the binding may be split by splitting the pattern and the corresponding expression.
-- The result is a map from subpatterns to subexpressions and the number of matches. 
-- If the number is -1 the subpattern cannot be substituted and must be retained in the original binding.
findMatches :: GenIrrefPatn -> GenExpr -> [GenBnd] -> GenExpr -> MatchMap
findMatches ip e ((CS.Binding ipp Nothing ep []) : bps) bdy =
  combineMatches [msp, ms]
  where msp = findMatches ip e [] ep
        ms = findMatchesUnderBinding ip e (freeInIrrefPatn ipp) bps bdy
findMatches _ _ (b : _) _ = error ("unexpected binding in letproc: " ++ (show b))
findMatches ip e [] bdy = 
    if null ivars 
       then M.empty
       else case reduceBinding ivars ip e of
                 Nothing -> M.singleton ip (-1,e)
                 Just (ip',e') -> findFullMatches ip' e' (exprOfGE bdy)
    where evars = freeInExpr e
          pvars = freeInIrrefPatn ip
          ivars = intersect evars pvars

-- | Find matches of a binding in an expression.
-- The binding binds only variables which occur free in the expression.
-- The binding binds at least one variable.
findFullMatches :: GenIrrefPatn -> GenExpr -> ExprOfGE -> MatchMap
findFullMatches ip e bdy@(CS.Var _) = M.singleton ip (cnt,e)
    where cnt = if matches (irpatnOfGIP ip) bdy then 1 else -1
findFullMatches ip e bdy@(CS.Tuple es) =
    if matches (irpatnOfGIP ip) bdy
       then M.singleton ip (1,e)
       else combineMatches $ map (findMatches ip e []) es
findFullMatches ip e (CS.Let bs bdy) = findMatches ip e bs bdy
findFullMatches ip e (CS.Match e' vs alts) =
    combineMatches [ms',ms]
    where ms' = findMatches ip e [] e'
          ms = combineMatches $ map (\(CS.Alt p _ bdy) -> findMatchesUnderBinding ip e (freeInPatn p) [] bdy) alts
findFullMatches ip e (CS.Lam ip' mt bdy) =
    findMatchesUnderBinding ip e (freeInIrrefPatn ip') [] bdy
findFullMatches ip e bdy =
    combineMatches $ map (findMatches ip e []) $ toList bdy

-- | Find matches in an expression which is under a binding of variables.
-- The bound variables must be removed from the pattern and expressions where they occur free must be retained.
-- The expression under the binding consists of additional bindings and a body.
findMatchesUnderBinding :: GenIrrefPatn -> GenExpr -> [VarName] -> [GenBnd] -> GenExpr -> MatchMap
findMatchesUnderBinding ip e vs bs bdy = 
    case splitBinding vs ip e of
           Nothing -> M.singleton ip (-1,e)
           Just (ip1,e1,ip2,e2) ->
              let ms1 = findMatches ip1 e1 bs bdy
                  ms2 = findMatches ip2 e2 bs bdy
              in combineMatches [ms1, retainOrDrop ms2]

-- | Match a pattern with an expression.
-- Currently only successful for nested variable tuple patterns.
-- This means that other patterns are never substituted by simplifying let expressions.
matches :: IrpatnOfGIP -> ExprOfGE -> Bool
matches (PVar v) (Var v') = v == v'
matches (PTuple ips) (Tuple es) = 
    (length ips) == (length es) && 
    (all (uncurry matches) $ zip (map irpatnOfGIP ips) (map exprOfGE es))
matches _ _ = False

-- | Free variables in a pattern.
freeInPatn :: GenPatn -> [VarName]
freeInPatn = nub . CS.fvP . toRawPatn

-- | Free variables in an irrefutable pattern.
freeInIrrefPatn :: GenIrrefPatn -> [VarName]
freeInIrrefPatn = nub . CS.fvIP . toRawIrrefPatn

-- | Free variables in an expression.
freeInExpr :: GenExpr -> [VarName]
freeInExpr = nub . CS.fvE . toRawExpr

-- | Free variables in the patterns of a MatchMap.
freeInMap :: MatchMap -> [VarName]
freeInMap m = nub $ concatMap freeInIrrefPatn $ M.keys m

-- | Reduce the binding consisting of the pattern and the expression according to a set of variables.
-- All parts are omitted which bind a variable not in the set. If such a splitting is not 
-- possible the result is Nothing.
-- The set contains at least one variable bound in the pattern, if the splitting is possible the result
-- is a nonempty binding.
reduceBinding :: [VarName] -> GenIrrefPatn -> GenExpr -> Maybe (GenIrrefPatn,GenExpr)
reduceBinding vs ip e = 
    if null vs'
       then Just (ip,e)
       else removeWildcards ip' e
    where vs' = (freeInIrrefPatn ip) \\ vs
          ip' = mapIrpatnOfGIP (replaceVarsInPattern vs') ip

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

-- | Remove wildcards from a pattern and remove the corresponding parts from a matching expression.
-- If the pattern only contains wildcards (i.e. binds no variable) it is replaced by a unit pattern.
-- If the pattern contains wildcards and variables and the expression cannot be split, the result is Nothing.
removeWildcards :: GenIrrefPatn -> GenExpr -> Maybe (GenIrrefPatn,GenExpr)
removeWildcards ip e = 
    if not $ containsWildcard ip
       then Just (ip,e)
       else if onlyWildcards ip
              then Just (mapIrpatnOfGIP (const PUnitel) ip,e)
              else case irpatnOfGIP ip of
                        -- must be structured since it contains wildcards and non-wildcards
                        PTuple ips -> removeWildcardsFromTuple ip ips e
                        -- we do not split records or arrays
                        _ -> Nothing
    where removeWildcardsFromTuple ip ips e = 
             case splitExpr e of
                  Nothing -> Nothing
                  Just es -> 
                    let bs = map (uncurry removeWildcards) $ zip ips es
                    in if any isNothing bs 
                          then Nothing
                          else Just $ toTupleBind (filter (\(ip,_) -> (irpatnOfGIP ip) /= PUnitel) $ catMaybes bs) ip e

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
         PTake v flds -> all (onlyWildcards . snd) (catMaybes flds)
         PArray ips -> all onlyWildcards ips
         PArrayTake v els -> all (onlyWildcards . snd) els

-- | Turn a nonempty sequence of bindings into a tuple binding.
-- If the sequence has length 1, its single binding is returned.
-- Otherwise the result reuses a given pattern and expression.
toTupleBind :: [(GenIrrefPatn,GenExpr)] -> GenIrrefPatn -> GenExpr -> (GenIrrefPatn,GenExpr)
toTupleBind bs ip e = 
    if (length bs) == 1
       then head bs
       else let ubs = unzip bs
            in (mapIrpatnOfGIP (const (PTuple (fst ubs))) ip,
                mapExprOfGE (const (Tuple (snd ubs))) e)

-- | Split an expression of tuple type into a list of expressions for the components.
-- If that is not possible return Nothing
-- A tuple expression can always be split.
-- The following expressions can be split if the relevant subexpressions can be split:
-- Match, Lam, If, MultiWayIf, Let. 
-- From these we only try to split If expressions.
splitExpr :: GenExpr -> Maybe [GenExpr]
splitExpr e = 
    case exprOfGE e of
         Tuple es -> Just es
         If c vs e1 e2 -> 
           let mes1 = splitExpr e1
               mes2 = splitExpr e2
           in if mes1 == Nothing || mes2 == Nothing 
                 then Nothing
                 else Just $ map (\(e1',e2') -> mapExprOfGE (const (If c vs e1' e2')) e) $ zip (fromJust mes1) (fromJust mes2)
         _ -> Nothing

-- | Split the binding consisting of the pattern and the expression according to a set of variables.
-- First all parts are omitted which bind a variable in the set. If such a splitting is not 
-- possible the result is Nothing.
-- Otherwise the remaining binding is split into a maximal part where no variable in the set 
-- occurs free in the expression and the rest part. If one of these parts is empty the corresponding 
-- pattern is the unit pattern.
splitBinding :: [VarName] -> GenIrrefPatn -> GenExpr -> Maybe (GenIrrefPatn,GenExpr,GenIrrefPatn,GenExpr)
splitBinding vs ip e = 
    if null vs
       then Just (ip, e, unitpattern, e)
       else case removeWildcards ip' e of
                 Nothing -> Nothing
                 Just (ip'',e') -> splitBinding' vs ip'' e'
    where ip' = mapIrpatnOfGIP (replaceVarsInPattern vs) ip
          unitpattern = mapIrpatnOfGIP (const (PUnitel)) ip
          splitBinding' vs ip e =
            let fvs = intersect vs $ freeInExpr e
            in if null fvs
                  then Just (ip, e, unitpattern, e)
                  else case irpatnOfGIP ip of
                            PTuple ips -> splitTuple vs ip ips e
                            _ -> Just (unitpattern, e, ip, e)
          splitTuple vs ip ips e =
            case splitExpr e of
                 Nothing -> Nothing
                 Just es -> 
                   let (nofree,free) = partition (\(ip,e) -> null $ intersect vs $ freeInExpr e) $ zip ips es
                   in if null nofree
                         then Just (unitpattern, e, ip, e)
                         else -- free cannot be empty because fvs was not null above
                              let (nfip,nfe) = toTupleBind nofree ip e
                                  (fip,fe) = toTupleBind free ip e
                              in Just (nfip,nfe,fip,fe)

-- | Combine match results.
-- If a pattern occurs in both maps the expressions are the same. The number of matches is -1 if 
-- it is -1 in either map, otherwise the sum of the matches in both maps.
combineMatches :: [MatchMap] -> MatchMap
combineMatches = 
    M.unionsWith (\(i1,e1) (i2,e2) -> (if i1 == -1 || i2 == -1 then -1 else i1+i2, e1))

-- | Drop sub bindings with 0 matches and retain all others
retainOrDrop :: MatchMap -> MatchMap
retainOrDrop m = 
    M.map (\(_,e) -> (-1,e)) $ M.filter (\(i,_) -> i == 0) m

