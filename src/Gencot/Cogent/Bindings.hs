{-# LANGUAGE PackageImports #-}
module Gencot.Cogent.Bindings where

import Data.List (union,nub,delete,(\\))
import Data.Maybe (catMaybes,isNothing)

import Cogent.Surface as CS
import Cogent.Common.Syntax as CCS

import Gencot.Cogent.Ast
import Gencot.Origin (noOrigin)
    
prime = '\''

ctlVar = "c"++[prime]

resVar = "r"++[prime]

swtVar = "s"++[prime]

casVar :: Int -> CCS.VarName
casVar n = "s"++(show n)++[prime]

cmpVar :: Int -> CCS.VarName
cmpVar n = "p"++(show n)++[prime]

idxVar :: Int -> CCS.VarName
idxVar n = "i"++(show n)++[prime]

valVar :: Int -> CCS.VarName
valVar 0 = "v"++[prime]
valVar n = "v"++(show n)++[prime]

-- A pair of main and putback binding lists.
-- The main list is represented in reverse order.
type BindsPair = ([GenBnd],[GenBnd])

-- | Convert a binding list pair for an expression to a binding list pair for a statement. 
etosBindsPair :: BindsPair -> BindsPair
etosBindsPair (main,putback) =
    ((mkVarBinding ctlVar $ mkIntLitExpr 0) : main, putback)

-- | Select side effect targets from a binding list pair.
sideEffectTargets :: BindsPair -> [CCS.VarName]
sideEffectTargets (main,putback) =
    sideEffectFilter $ union (boundVarsList main) (boundVarsList putback)

-- | Select side effect targets from a list of variable names.
sideEffectFilter :: [CCS.VarName] -> [CCS.VarName]
sideEffectFilter vs =
    filter (\v -> (last v) /= prime || v == resVar) vs 

-- | All variable names occurring in a pattern.
tupleVars :: GenIrrefPatn -> [CCS.VarName]
tupleVars ip = case irpatnOfGIP ip of
                    CS.PVar v -> [v]
                    CS.PTuple pvs -> concat $ map tupleVars pvs
                    CS.PTake v fs -> v : (concat $ map (tupleVars . snd) $ catMaybes fs)
                    CS.PArrayTake v fs -> v : (concat $ map (tupleVars . snd) fs)

-- | Variable names bound in a binding
boundVars :: GenBnd -> [CCS.VarName]
boundVars (CS.Binding ip _ _ _) = tupleVars ip

-- | Variable names bound in a binding list
boundVarsList :: [GenBnd] -> [CCS.VarName]
boundVarsList bs = nub $ concat $ map boundVars bs

-- | The first variable bound in the final binding of the main list.
leadVar :: BindsPair -> CCS.VarName
leadVar (main,_) = head $ tupleVars ip
    where (CS.Binding ip _ _ _) = head main

isStatBindsPair :: BindsPair -> Bool
isStatBindsPair bp = (leadVar bp) == ctlVar

boundExpr :: GenBnd -> GenExpr
boundExpr (CS.Binding _ _ e _) = e

-- | The first expression bound in the final binding of the main list, if it is a variable.
lvalVar :: BindsPair -> Maybe CCS.VarName
lvalVar (main,_) = 
    case exprOfGE e of
         (CS.Tuple es) -> 
            case exprOfGE $ head es of
                 (CS.Var v) -> Just v
                 _ -> Nothing
         (CS.Var v) -> Just v
         _ -> Nothing
    where (CS.Binding _ _ e _) = head main

-- Construct Binding List Pairs
-------------------------------

mkEmptyBindsPair :: BindsPair
mkEmptyBindsPair = ([],[])

-- | Construct a binding list pair from a single binding.
mkSingleBindsPair :: GenBnd -> BindsPair
mkSingleBindsPair b = ([b],[])

-- | Single binding v<n>' = gencotDummy msg
mkDummyBindsPair :: Int -> String -> BindsPair
mkDummyBindsPair n msg = mkSingleBindsPair $ mkVarBinding (valVar n) $ mkDummyExpr msg

-- | Single binding v<n>' = ()
mkUnitBindsPair :: Int -> BindsPair
mkUnitBindsPair n = mkSingleBindsPair $ mkVarBinding (valVar n) $ mkUnitExpr

-- | Single binding v<n>' = defaultVal ()
mkDefaultBindsPair :: Int -> BindsPair
mkDefaultBindsPair n = mkSingleBindsPair $ mkVarBinding (valVar n) $ mkAppExpr "defaultVal" []

-- | Single binding v<n>' = i
mkIntLitBindsPair :: Int -> Integer -> BindsPair
mkIntLitBindsPair n i = mkSingleBindsPair $ mkVarBinding (valVar n) $ mkIntLitExpr i

-- | Single binding v<n>' = c
mkCharLitBindsPair :: Int -> Char -> BindsPair
mkCharLitBindsPair n i = mkSingleBindsPair $ mkVarBinding (valVar n) $ mkCharLitExpr i

-- | Single binding v<n>' = s
mkStringLitBindsPair :: Int -> String -> BindsPair
mkStringLitBindsPair n s = mkSingleBindsPair $ mkVarBinding (valVar n) $ mkStringLitExpr s

-- | Single binding v<n>' = v
mkValVarBindsPair :: Int -> CCS.VarName -> BindsPair
mkValVarBindsPair n v = mkSingleBindsPair $ mkVarBinding (valVar n) $ mkVarExpr v

-- | Member (field) access <v>{f=r<k>’} = v<n>' and v<n>’ = r<k>’
--   with putback <v> = <v>{f=r<k>’}
mkMemBindsPair :: Int -> CCS.FieldName -> BindsPair -> BindsPair
mkMemBindsPair n f bp = 
    if rv == "_" then mainbp else addPutback (mkVarBinding rv $ mkRecPutExpr rv cmp f) mainbp
    where cmp = cmpVar n
          vv = leadVar bp
          rv = case lvalVar bp of 
                    Just v -> v
                    Nothing -> "_"
          mainbp = addBinding (mkVarBinding vv $ mkVarExpr cmp) $ 
                     addBinding (mkBinding (mkRecTakePattern rv cmp f) $ mkVarExpr vv) bp

-- | Array access (<v> @{@v<l>’=r<k>’},i<k>') = (v<n>',v<l>') and v<n>’ = r<k>’
--   with putback <v> = <v> @{@i<k>'=r<k>’}
mkIdxBindsPair :: Int -> BindsPair -> BindsPair -> BindsPair
mkIdxBindsPair n bp1 bp2 = 
    if rv == "_" then mainbp else addPutback (mkVarBinding rv $ mkArrPutExpr rv cmp idx) mainbp
    where cmp = cmpVar n
          idx = idxVar n
          v1 = leadVar bp1
          v2 = leadVar bp2
          rv = case lvalVar bp1 of 
                    Just v -> v
                    Nothing -> "_"
          mainbp = addBinding (mkVarBinding v1 $ mkVarExpr cmp) $ 
                     addBinding (mkBinding (mkArrTakePattern rv cmp idx v2) $ mkVarTupleExpr [v1,v2]) $ concatBindsPairs [bp2,bp1]

-- | Operator application v<n>' = op [bp...]
mkOpBindsPair :: CCS.OpName -> [BindsPair] -> BindsPair
mkOpBindsPair op bps =
    addBinding (mkVarBinding (head vs) $ mkOpExpr op (map mkVarExpr vs)) $ concatBindsPairs bps
    where vs = map leadVar bps 

-- | Function application v = f (bp...) or (v,v1,..,vn) = f (bp..,vi,..,vn)
-- The third argument is the variable to bind the function result, or the empty string if the function has result type void.
-- The fourth argument is a boolean vector marking the Add-Result arguments in bps.
-- The fifth argument is the list of additional variables for Global-State and Heap-Use arguments,
-- each with a flag whether it shall be returned as result.
mkAppBindsPair :: CCS.FunName -> [BindsPair] -> CCS.VarName -> [Bool] -> [(CCS.VarName,Bool)] -> BindsPair
mkAppBindsPair f bps v ars ghs =
    if any isNothing marvs
       then mkSingleBindsPair $ mkVarBinding (head rvs) $ mkDummyExpr "Unsupported Add-Result argument"
       else addBinding (mkVarsBinding rvs $ mkAppExpr f (map mkVarExpr vs)) $ concatBindsPairs bps
    where vs = (map leadVar bps) ++ (map fst ghs)
          marvs = map lvalVar $ map snd $ filter fst $ zip ars bps
          argvs = (catMaybes marvs) ++ (map fst $ filter snd ghs)
          rvs = (if null v 
                   then if null argvs then ["_"] else []
                   else [v]) ++ argvs

-- | Assignment v<n>' = v<n>' op v<k>', (v<n>',v) = (v<n>',v<n>') or (v,v<n>')
-- The first argument is True for a postfix inc/dec operator, otherwise false.
-- The second argument is empty for a plain assignment, otherwise the operator op to be used.
-- The third argument is the lvalue BindsPair.
-- The fourth argument is the operator argument BindsPair or the assigned BindsPair for a plain assignment. 
mkAssBindsPair :: Bool -> CCS.OpName -> BindsPair -> BindsPair -> BindsPair
mkAssBindsPair post op bpl bpr =
    case lvalVar bpl of 
         Nothing -> mkSingleBindsPair $ mkVarBinding vl $ mkDummyExpr "Unsupported lvalue in assignment"
         Just v -> let e = mkVarExpr v
                       lval = mkVarsTupleBinding [vl,v] [if post then e else el, el]
                   in addBinding lval $ addBinding (mkVarBinding vl er') $ concatBindsPairs [bpr,bpl]
    where vl = leadVar bpl
          vr = leadVar bpr
          el = mkVarExpr vl
          er = mkVarExpr vr
          er' = if null op then er else mkOpExpr op [el,er]

-- | Conditional v<n>' = if bp1 then bp2 else bp3
mkIfBindsPair :: BindsPair -> BindsPair -> BindsPair -> BindsPair
mkIfBindsPair bp0 bp1 bp2 =
    addBinding (mkVarsBinding (v0 : set) (mkIfExpr (mkVarExpr v0) e1 e2)) bp
    where set1 = sideEffectTargets bp1
          set2 = sideEffectTargets bp2
          v0 = leadVar bp0
          set = union set1 set2
          (bp1l,e1) = if null set1
                         then ([bp1],mkVarTupleExpr (leadVar bp1 : set))
                         else ([],boundExpr $ cmbExtBinds set bp1)
          (bp2l,e2) = if null set2
                         then ([bp2],mkVarTupleExpr (leadVar bp2 : set))
                         else ([],boundExpr $ cmbExtBinds set bp2)
          bp = concatBindsPairs (bp0 : (bp1l ++ bp2l))

-- | Add binding to the main list
addBinding :: GenBnd -> BindsPair -> BindsPair
addBinding b (main,putback) = (b : main,putback)

-- | Add binding to the putback list
addPutback :: GenBnd -> BindsPair -> BindsPair
addPutback b (main,putback) = (main, b : putback)

-- | Concatenate binding list pairs in order.
-- The first binding list pair is evaluated first and putback last.
concatBindsPairs :: [BindsPair] -> BindsPair
concatBindsPairs bps = (concat mains,concat putbacks)
    where (mains,putbacks) = unzip $ reverse bps

-- Construct Bindings
---------------------

-- construct p = expr
mkBinding :: GenIrrefPatn -> GenExpr -> GenBnd
mkBinding ip e = CS.Binding ip Nothing e []

-- | Single binding c' = gencotDummy msg
mkDummyBinding :: String -> GenBnd
mkDummyBinding msg = mkVarBinding ctlVar $ mkDummyExpr msg

-- construct (p1,..,pn) = expr or p1 = expr
mkTupleBinding :: [GenIrrefPatn] -> GenExpr -> GenBnd
mkTupleBinding ps e = mkBinding (mkTuplePattern ps) e

-- construct (v1,..,vn) = expr or v1 = expr
mkVarsBinding :: [CCS.VarName] -> GenExpr -> GenBnd
mkVarsBinding vs e = mkTupleBinding (map mkVarPattern vs) e

-- construct v = expr
mkVarBinding :: CCS.VarName -> GenExpr -> GenBnd
mkVarBinding v e = mkBinding (mkVarPattern v) e

-- construct (v1,..,vn) = (e1,..,en)
mkVarsTupleBinding :: [CCS.VarName] -> [GenExpr] -> GenBnd
mkVarsTupleBinding [v] [e] = mkVarBinding v e
mkVarsTupleBinding vs es = mkVarsBinding vs $ mkTupleExpr es

-- replace p in (p,p1,...,pn) = expr or p = expr
replaceLeadPatn :: GenIrrefPatn -> GenBnd -> GenBnd
replaceLeadPatn ip (CS.Binding (GenIrrefPatn (CS.PTuple ps) _) _ e _) = mkTupleBinding (ip : tail ps) e
replaceLeadPatn ip' (CS.Binding ip _ e _) = mkBinding ip' e

-- | Null statement: c' = 0
mkNullBinding :: GenBnd
mkNullBinding = mkVarBinding ctlVar $ mkIntLitExpr 0

-- | Expression statement: (c',v1..) = let ... in (0,v1..)
mkExpBinding :: BindsPair -> GenBnd
mkExpBinding bp = mkVarsBinding (ctlVar : vs) $ mkLetExpr [cmbBinds bp] $ mkCtlVarTupleExpr 0 vs
    where vs = sideEffectTargets bp

-- | Return statement: (c',r',v1..) = let ... in (3, v<n>',v1,..)
mkRetBinding :: BindsPair -> GenBnd
mkRetBinding bp = mkVarsBinding (ctlVar : (resVar : vs)) $ mkLetExpr [cmbBinds bp] $ mkCtlVarTupleExpr 3 (v : vs)
    where v = leadVar bp
          vs = sideEffectTargets bp

-- | Break statement: c' = 2
mkBreakBinding :: GenBnd
mkBreakBinding = mkVarBinding ctlVar $ mkIntLitExpr 2

-- | Continue statement: c' = 1
mkContBinding :: GenBnd
mkContBinding = mkVarBinding ctlVar $ mkIntLitExpr 1

-- | Conditional statement (c',z1..) = let (v<n>',v1..) = expr in if v<n>' then let b1 in (c',z1..) else let b2 in (c',z1..)
mkIfBinding :: BindsPair -> GenBnd -> GenBnd -> GenBnd
mkIfBinding bp b1 b2 =
    mkVarsBinding vs $ mkLetExpr [cmbBinds bp] $ mkIfExpr (mkVarExpr (leadVar bp)) e1 e2
    where set0 = sideEffectTargets bp
          set1 = sideEffectFilter $ boundVars b1
          set2 = sideEffectFilter $ boundVars b2
          vs = ctlVar : (union set0 $ union set1 set2)
          e1 = mkLetExpr [b1] $ mkVarTupleExpr vs
          e2 = mkLetExpr [b2] $ mkVarTupleExpr vs

-- | Switch statement (c',z1..) = let (s',v1..) = expr and (s1',...) = (s' == expr1,...) 
--         and (c',x1..) = exprb in (if c'=2 then 0 else c',z1..)
-- mbps are the case label expression binding list pairs with Nothing representing the default statement.
mkSwitchBinding :: BindsPair -> [Maybe BindsPair] -> GenBnd -> GenBnd
mkSwitchBinding bp mbps b =
    mkVarsBinding (ctlVar : vs) $ mkLetExpr [bp',mbps',b] $ mkExpVarTupleExpr c vs
    where set0 = sideEffectTargets bp
          set1 = sideEffectFilter $ boundVars b
          vs = union set0 set1
          bp' = replaceLeadPatn (mkVarPattern swtVar) $ cmbBinds bp
          casVars = map casVar $ take (length mbps) $ iterate (1+) 1
          casVal Nothing = mkBoolLitExpr True
          casVal (Just bp) = mkOpExpr "==" [mkVarExpr swtVar, mkPlainExpr bp]
          mbps' = mkVarsTupleBinding casVars $ map casVal mbps
          c = mkIfExpr (mkOpExpr "==" [mkVarExpr ctlVar,mkIntLitExpr 2]) (mkIntLitExpr 0) (mkVarExpr ctlVar)

-- | Switch group (c',x1..) = if cond then let b in (c',x1..) else (0,x1..)
mkCaseBinding :: GenBnd -> Int -> Int -> Bool -> GenBnd
mkCaseBinding b nr grps dfltSeen = 
    if dfltSeen && nr == grps
       then mkVarsBinding vs $ mkLetExpr [b] $ mkVarTupleExpr vs
       else mkVarsBinding vs $ mkIfExpr (cond dfltSeen) (mkLetExpr [b] $ mkVarTupleExpr vs) $ mk0VarTupleExpr set
    where set = sideEffectFilter $ boundVars b
          vs = ctlVar : set
          cond False = mkDisjExpr $ map (mkVarExpr . casVar) $ take nr $ iterate (1+) 1
          cond True = mkOpExpr "not" [mkDisjExpr $ map (mkVarExpr . casVar) $ take (grps-nr) $ iterate (1+) (nr+1)]

-- | Statement in Sequence (c',z1..) = let b in if c' > 0 then (c',z1..) else let bs in (c',z1..)
mkSeqBinding :: GenBnd -> GenBnd -> GenBnd
mkSeqBinding b bs =
    mkVarsBinding vs $ mkLetExpr [b] $ 
      mkIfExpr (mkOpExpr ">" [mkVarExpr ctlVar,mkIntLitExpr 0]) e $ mkLetExpr [bs] $ e
    where set1 = sideEffectFilter $ boundVars b
          set2 = sideEffectFilter $ boundVars bs
          vs = ctlVar : (union set1 set2)
          e = mkVarTupleExpr vs

-- | Jump-free statement in sequence (c’,z1..) = let b and bs in (c’,z1..)
mkSimpSeqBinding :: GenBnd -> GenBnd -> GenBnd
mkSimpSeqBinding b bs =
    mkVarsBinding vs $ mkLetExpr [b, bs] $ mkVarTupleExpr vs
    where set1 = sideEffectFilter $ boundVars b
          set2 = sideEffectFilter $ boundVars bs
          vs = ctlVar : (union set1 set2)

-- | Declarator in Sequence 
-- (c’,z1..) = let (v<n>’,v1..) = expr and (c’,u1..) = let v = v<n>’ and b in (c’,u1..) in (c’,z1..)
mkDecBinding :: CCS.VarName -> BindsPair -> GenBnd -> GenBnd
mkDecBinding v bp b = 
    mkVarsBinding vs $ mkLetExpr [cmbBinds bp, mkVarsBinding vs' e] $ mkVarTupleExpr vs
    where setv = sideEffectTargets bp
          sety = sideEffectFilter $ boundVars b
          setu = delete v sety
          setz = union setv setu
          vs = ctlVar : setz
          vs' = ctlVar : setu
          e = mkLetExpr [mkVarBinding v $ mkVarExpr $ leadVar bp, b] $ mkVarTupleExpr vs'

-- | Declaration as sequence of declarators
mkDeclBinding :: [(CCS.VarName,BindsPair)] -> GenBnd -> GenBnd
mkDeclBinding [] b = b
mkDeclBinding ((v,bp) : ds) b = mkDecBinding v bp $ mkDeclBinding ds b

-- | for statement: 
mkForBinding :: BindsPair -> (Either (Maybe BindsPair) [(CCS.VarName,BindsPair)]) -> BindsPair -> BindsPair -> GenBnd -> [CCS.VarName] -> GenBnd
mkForBinding bpm ebp1 bp2 bp3 b freevars = 
    case ebp1 of
         (Left Nothing) -> bindloop
         (Left (Just bp1)) -> mkSimpSeqBinding (cmbBinds bp1) bindloop
         (Right ds) -> mkDeclBinding ds bindloop
    where b3 = cmbBinds bp3
          accvars = union (sideEffectFilter $ boundVars b) (sideEffectFilter $ boundVars b3)
          obsvars = freevars \\ accvars
          exprstep = mkLetExpr [b] $ mkIfExpr ctlcond accexpr $ mkLetExpr [b3] $ mk0VarTupleExpr accvars
          b2 = cmbBinds bp2
          exprloop = mkLetExpr [(mkBinding accpat $ mkAppExpr "repeat" [repeatargexpr])] $ mkExpVarTupleExpr repeatctl accvars
          accpat = mkPatVarTuplePattern mkCtrlPattern accvars -- (c',y1..)
          accexpr = mkVarTupleExpr (ctlVar : accvars) -- (c',y1..)
          ctlcond = mkOpExpr ">" [mkVarExpr ctlVar,mkIntLitExpr 1] -- c' > 1
          accpatwild = mkPatVarTuplePattern mkWildcardPattern accvars -- (_,y1..)
          obsvpat = mkVarTuplePattern obsvars
          repeatctl = mkIfExpr (mkOpExpr "==" [mkVarExpr ctlVar,mkIntLitExpr 2]) (mkIntLitExpr 0) (mkVarExpr ctlVar)
          repeatargexpr = mkRecordExpr [("n",exprmax),("stop",stopfun),("step",stepfun),("acc",iniacc),("obsv",iniobsv)]
          exprmax = mkPlainExpr bpm
          iniacc = mk0VarTupleExpr accvars
          iniobsv = mkVarTupleExpr obsvars
          stopfun = mkLambdaExpr (mkRecordPattern [("acc",accpat),("obsv",obsvpat)]) $ mkLetExpr [b2] stopexpr
          stopexpr = mkDisjExpr [ctlcond, mkOpExpr "not" [mkVarExpr $ leadVar bp2]]
          stepfun = mkLambdaExpr (mkRecordPattern [("acc",accpatwild),("obsv",obsvpat)]) exprstep
          bindloop = mkBinding accpat exprloop

-- | Combine all bindings in a binding list pair to a single binding.
-- (v<n>',v1..) = let ... in (v<n>',v1..)
cmbBinds :: BindsPair -> GenBnd
cmbBinds bp = cmbExtBinds (sideEffectTargets bp) bp

-- | Combine all bindings in a binding list pair to a single binding with given side effect targets.
cmbExtBinds :: [CCS.VarName] -> BindsPair -> GenBnd
cmbExtBinds vs bp@(main,putback) = 
    mkVarsBinding vs' $ mkLetExpr bs $ mkVarTupleExpr vs'
    where lv = leadVar bp
          vs' = if elem lv vs then vs else lv : vs
          bs = (reverse main) ++ putback

-- Construct Patterns
---------------------

genIrrefPatn p = GenIrrefPatn p noOrigin

mkWildcardPattern :: GenIrrefPatn
mkWildcardPattern = genIrrefPatn CS.PUnderscore

mkVarPattern :: CCS.VarName -> GenIrrefPatn
mkVarPattern = genIrrefPatn . CS.PVar

mkCtrlPattern :: GenIrrefPatn
mkCtrlPattern = mkVarPattern ctlVar

mkValPattern :: Int -> GenIrrefPatn
mkValPattern = mkVarPattern . valVar

mkTuplePattern :: [GenIrrefPatn] -> GenIrrefPatn
mkTuplePattern [ip] = ip
mkTuplePattern ips = genIrrefPatn $ CS.PTuple ips

-- construct (v1,..,vn)
mkVarTuplePattern :: [CCS.VarName] -> GenIrrefPatn
mkVarTuplePattern vs = mkTuplePattern $ map mkVarPattern vs

-- construct (p,v1,..,vn)
mkPatVarTuplePattern :: GenIrrefPatn -> [CCS.VarName] -> GenIrrefPatn
mkPatVarTuplePattern p vs = mkTuplePattern (p : map mkVarPattern vs)

-- construct #{f1 = p1, ..., fn = pn}
mkRecordPattern :: [(CCS.FieldName,GenIrrefPatn)] -> GenIrrefPatn
mkRecordPattern flds = genIrrefPatn $ CS.PUnboxedRecord $ map Just flds

-- construct v1{m=v2}
mkRecTakePattern :: CCS.VarName -> CCS.VarName -> CCS.FieldName -> GenIrrefPatn
mkRecTakePattern v1 v2 m = genIrrefPatn $ CS.PTake v1 [Just (m, mkVarPattern v2)]

-- construct (v1 @{@v4=v2},v3)
mkArrTakePattern :: CCS.VarName -> CCS.VarName -> CCS.VarName -> CCS.VarName -> GenIrrefPatn
mkArrTakePattern v1 v2 v3 v4 = mkTuplePattern [genIrrefPatn $ CS.PArrayTake v1 [(mkVarExpr v4,mkVarPattern v2)], mkVarPattern v3]

-- Construct Expressions
------------------------

genExpr e = GenExpr e noOrigin Nothing

-- construct ()
mkUnitExpr :: GenExpr
mkUnitExpr = genExpr CS.Unitel

-- construct i
mkIntLitExpr :: Integer -> GenExpr
mkIntLitExpr = genExpr . CS.IntLit

-- construct c
mkCharLitExpr :: Char -> GenExpr
mkCharLitExpr = genExpr . CS.CharLit

-- construct s
mkStringLitExpr :: String -> GenExpr
mkStringLitExpr = genExpr . CS.StringLit

-- construct True or False
mkBoolLitExpr :: Bool -> GenExpr
mkBoolLitExpr = genExpr . CS.BoolLit

-- construct v
mkVarExpr :: CCS.VarName -> GenExpr
mkVarExpr = genExpr . CS.Var

-- construct (e1,..,en) or e1
mkTupleExpr :: [GenExpr] -> GenExpr
mkTupleExpr [e] = e
mkTupleExpr es = genExpr $ CS.Tuple es

-- construct e1 op e2 or op e1
mkOpExpr :: CCS.OpName -> [GenExpr] -> GenExpr
mkOpExpr op es = genExpr $ CS.PrimOp op es

-- construct (<control value>,v1,...,vn) or <control value>
mkCtlVarTupleExpr :: Integer -> [CCS.VarName] -> GenExpr
mkCtlVarTupleExpr cv vs = mkExpVarTupleExpr (mkIntLitExpr cv) vs

-- construct (v1,...,vn) or v1
mkVarTupleExpr :: [CCS.VarName] -> GenExpr
mkVarTupleExpr vs = mkTupleExpr $ map mkVarExpr vs

-- construct (e,v1,...,vn) or e
mkExpVarTupleExpr :: GenExpr -> [CCS.VarName] -> GenExpr
mkExpVarTupleExpr e [] = e
mkExpVarTupleExpr e vs = mkTupleExpr (e : (map mkVarExpr vs))

-- construct (0,v1,...,vn) or 0
mk0VarTupleExpr :: [CCS.VarName] -> GenExpr
mk0VarTupleExpr vs = mkExpVarTupleExpr (mkIntLitExpr 0) vs

-- construct e1 || ... || en
mkDisjExpr :: [GenExpr] -> GenExpr
mkDisjExpr [] = mkBoolLitExpr False
mkDisjExpr [e] = e
mkDisjExpr (e : es) = mkOpExpr "||" [e,mkDisjExpr es]

-- replace e1 in (e1,...,en) or e1
replaceLeadExpr :: GenExpr -> GenExpr -> GenExpr
replaceLeadExpr e (GenExpr (CS.Tuple es) o src) = GenExpr (CS.Tuple (e : tail es)) o src
replaceLeadExpr e _ = e

-- construct f () or f e1 or f (e1,..,en)
mkAppExpr :: CCS.FunName -> [GenExpr] -> GenExpr
mkAppExpr f es = genExpr $ CS.App (genExpr $ CS.Var f) (arg es) False
    where arg [] = mkUnitExpr
          arg [e] = e
          arg es = mkTupleExpr es

-- construct f[t1..] () or f[t1..] e1 or f[t1..] (e1,..,en)
mkTypedAppExpr :: CCS.FunName -> [Maybe GenType] -> [GenExpr] -> GenExpr
mkTypedAppExpr f ts es = genExpr $ CS.App (genExpr $ CS.TLApp f ts [] NoInline) (arg es) False
    where arg [] = mkUnitExpr
          arg [e] = e
          arg es = mkTupleExpr es

-- construct let b1 and ... and bn in e
mkLetExpr :: [GenBnd] -> GenExpr -> GenExpr
mkLetExpr bs e =
    genExpr $ CS.Let bs e

-- construct v1{f=v2}
mkRecPutExpr :: CCS.VarName -> CCS.VarName -> CCS.FieldName -> GenExpr
mkRecPutExpr v1 v2 f = genExpr $ CS.Put (mkVarExpr v1) [Just (f,mkVarExpr v2)]

-- construct v1 @{@v3=v2}
mkArrPutExpr :: CCS.VarName -> CCS.VarName -> CCS.FieldName -> GenExpr
mkArrPutExpr v1 v2 v3 = genExpr $ CS.ArrayPut (mkVarExpr v1) [(mkVarExpr v3,mkVarExpr v2)]

-- construct if e0 then e1 else e2
mkIfExpr :: GenExpr -> GenExpr -> GenExpr -> GenExpr
mkIfExpr e0 e1 e2 = genExpr $ CS.If e0 [] e1 e2

-- construct e | C1 v11 .. v1n1 -> e1 | ... | Ck vk1 .. vknk -> ek
mkMatchExpr :: GenExpr -> [(CCS.TagName,[CCS.VarName],GenExpr)] -> GenExpr
mkMatchExpr e as = genExpr $ CS.Match e [] $ map mkAlt as
    where mkAlt (tag,vars,e) = CS.Alt (GenPatn (CS.PCon tag $ map mkVarPattern vars) noOrigin) CCS.Regular e

-- construct #{f1 = e1, ... ,fn = en}
mkRecordExpr :: [(CCS.FieldName,GenExpr)] -> GenExpr
mkRecordExpr flds = genExpr $ CS.UnboxedRecord flds

-- construct \p => e
mkLambdaExpr :: GenIrrefPatn -> GenExpr -> GenExpr
mkLambdaExpr p e = genExpr $ CS.Lam p Nothing e

-- construct let (_,...) = expr in e
mkBodyExpr :: GenBnd -> GenExpr -> GenExpr
mkBodyExpr b e = mkLetExpr [replaceLeadPatn mkWildcardPattern b] e

-- construct let ... in v<n>'
mkPlainExpr :: BindsPair -> GenExpr
mkPlainExpr (main,putback) = 
    if not $ null putback
       then toDummyExpr e $ mkDummyExpr "No putback obligations supported in plain expression."
       else 
       if (length vs) > 1
          then toDummyExpr e $ mkDummyExpr "No side effects supported in plain expression."
          else mkLetExpr (reverse main) $ mkVarExpr $ head vs
    where (CS.Binding ip _ e _) = head main
          vs = tupleVars ip

-- construct (gencotDummy msg)
mkDummyExpr :: String -> GenExpr
mkDummyExpr msg = mkAppExpr "gencotDummy" [mkStringLitExpr msg]

-- turn expression to dummy, preserving origin and source
toDummyExpr :: GenExpr -> GenExpr -> GenExpr
toDummyExpr (GenExpr e o src) (GenExpr dummy _ _) = (GenExpr dummy o src) 
