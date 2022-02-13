{-# LANGUAGE PackageImports #-}
module Gencot.Cogent.Simplify where

import Data.List (concatMap,nub,intersect)
import qualified Data.Map as M
import Data.Maybe (catMaybes)
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
          bps'' = if M.null retain then bps' else (retainBind retain) : bps'

type MatchMap = M.Map GenIrrefPatn (Int,GenExpr)

-- | Substitute matches from the map in an expression.
-- The expression corresponds to a let expression consisting of the bindings and the body expression.
-- The result is the same expression with substituted matches, as a pair of the bindings and the body expression.
-- The map contains only matches which can be substituted in the expression.
-- (TODO)
substMatches :: MatchMap -> [GenBnd] -> GenExpr -> ([GenBnd],GenExpr)
substMatches m bs bdy = (bs,bdy)

-- | Convert a map of matches to be retained to a binding.
-- (TODO)
retainBind :: MatchMap -> GenBnd
retainBind m = CS.Binding ip Nothing e []
    where (ip,(_,e)) = head $ M.toList m

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
        ms = case splitBinding (freeInIrrefPatn ipp) ip e of
               Nothing -> M.singleton ip (-1,e)
               Just (ip1,e1,ip2,e2) ->
                  let ms1 = findMatches ip1 e1 bps bdy
                      ms2 = findMatches ip2 e2 bps bdy
                  in combineMatches [ms1, retainOrDrop ms2]
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
findFullMatches ip e bdy@(Var _) = M.singleton ip (cnt,e)
    where cnt = if matches (irpatnOfGIP ip) bdy then 1 else -1
findFullMatches ip e bdy@(Tuple es) =
    if matches (irpatnOfGIP ip) bdy
       then M.singleton ip (1,e)
       else combineMatches $ map (findMatches ip e []) es
findFullMatches ip e bdy@(Let bs bdy') = findMatches ip e bs bdy'
-- (TODO) other special cases??
findFullMatches ip e bdy =
    combineMatches $ map (findMatches ip e []) $ toList bdy

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
freeInIrrefPatn :: GenIrrefPatn -> [VarName]
freeInIrrefPatn = nub . CS.fvIP . toRawIrrefPatn

-- | Free variables in an expression.
freeInExpr :: GenExpr -> [VarName]
freeInExpr = nub . CS.fvE . toRawExpr

-- | Reduce the binding consisting of the pattern and the expression according to a set of variables.
-- All parts are omitted which bind a variable not in the set. If such a splitting is not 
-- possible the result is Nothing.
-- (TODO)
reduceBinding :: [VarName] -> GenIrrefPatn -> GenExpr -> Maybe (GenIrrefPatn,GenExpr)
reduceBinding vs ip e = Nothing

-- | Split the binding consisting of the pattern and the expression according to a set of variables.
-- First all parts are omitted which bind a variable in the set. If such a splitting is not 
-- possible the result is Nothing.
-- Otherwise the remaining binding is split into a maximal part where no variable in the set 
-- occurs free in the expression and the rest part.
-- (TODO)
splitBinding :: [VarName] -> GenIrrefPatn -> GenExpr -> Maybe (GenIrrefPatn,GenExpr,GenIrrefPatn,GenExpr)
splitBinding vs ip e = Nothing

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

