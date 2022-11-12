{-# LANGUAGE PackageImports #-}
module Gencot.Cogent.Bindings where

import Data.List (union,nub,delete,(\\))
import Data.Maybe (catMaybes,isNothing)

import Cogent.Surface as CS
import Cogent.Common.Syntax as CCS

import Gencot.Origin (noOrigin)
import Gencot.Cogent.Ast -- includes unitType
import Gencot.Cogent.Types (
  mkU8Type, mkU32Type, mkStringType, mkBoolType, 
  mkTupleType, mkCtlType, mkFunType, mkRecordType, mkTakeType, mkArrTakeType, 
  getMemType, getResultType,
  isFunctionType)
import Gencot.Cogent.Expr (
  TypedVar, TypedFun,
  mkUnitExpr, mkIntLitExpr, mkCharLitExpr, mkStringLitExpr, mkBoolLitExpr,
  mkVarExpr, mkCtlLitExpr, mkTupleExpr, mkOpExpr, mkBoolOpExpr, mkCtlVarTupleExpr, mkVarTupleExpr, mkExpVarTupleExpr, mk0VarTupleExpr,
  mkDisjExpr, mkAppExpr, mkLetExpr, mkRecPutExpr, mkArrPutExpr,
  mkIfExpr, mkRecordExpr, mkLambdaExpr, mkPlainExpr, mkDummyExpr)

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

typedCtlVar = (ctlVar, mkCtlType)
typedCasVar n = (casVar n, mkBoolType)

-- A pair of main and putback binding lists.
-- The main list is represented in reverse order.
type BindsPair = ([GenBnd],[GenBnd])

-- | Convert a binding list pair for an expression to a binding list pair for a statement. 
etosBindsPair :: BindsPair -> BindsPair
etosBindsPair (main,putback) =
    ((mkVarBinding typedCtlVar $ mkCtlLitExpr 0) : main, putback)

-- | Select side effect targets from a binding list pair.
-- For the actually occurring BindsPairs all resulting variables should have different names,
-- because they are mapped from C identifiers occurring in the same block, so every occurrence has the same type.
sideEffectTargets :: BindsPair -> [TypedVar]
sideEffectTargets (main,putback) =
    sideEffectFilter $ union (boundVarsList main) (boundVarsList putback)

-- | Select side effect targets from a list of typed variables.
sideEffectFilter :: [TypedVar] -> [TypedVar]
sideEffectFilter vs =
    filter (\(v,_) -> (last v) /= prime || v == resVar) vs 

-- | All typed variables occurring in a pattern.
tupleVars :: GenIrrefPatn -> [TypedVar]
tupleVars ip = case irpatnOfGIP ip of
                    CS.PVar v -> [(v,typOfGIP ip)]
                    CS.PTuple pvs -> concat $ map tupleVars pvs
                    CS.PTake v fs -> (v,mkTakeType True (typOfGIP ip) (map fst $ catMaybes fs)) : (concat $ map (tupleVars . snd) $ catMaybes fs)
                    CS.PArrayTake v fs -> (v, mkArrTakeType True (typOfGIP ip) (map fst fs)) : (concat $ map (tupleVars . snd) fs)

-- | Typed variables bound in a binding
-- For a valid binding all resulting variables have different names.
boundVars :: GenBnd -> [TypedVar]
boundVars (CS.Binding ip _ _ _) = tupleVars ip

-- | Typed variables bound in a binding list
-- The result may contain variables with the same name but different types.
boundVarsList :: [GenBnd] -> [TypedVar]
boundVarsList bs = nub $ concat $ map boundVars bs

-- | The first typed variable bound in the final binding of the main list.
leadVar :: BindsPair -> TypedVar
leadVar (main,_) = head $ tupleVars ip
    where (CS.Binding ip _ _ _) = head main

isStatBindsPair :: BindsPair -> Bool
isStatBindsPair bp = (fst (leadVar bp)) == ctlVar

boundExpr :: GenBnd -> GenExpr
boundExpr (CS.Binding _ _ e _) = e

-- | The first expression bound in the final binding of the main list, if it is a variable.
lvalVar :: BindsPair -> Maybe TypedVar
lvalVar (main,_) = 
    case exprOfGE e of
         (CS.Tuple es) -> 
            case exprOfGE $ head es of
                 (CS.Var v) -> Just (v,typOfGE $ head es)
                 _ -> Nothing
         (CS.Var v) -> Just (v,typOfGE e)
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
mkDummyBindsPair n msg = mkSingleBindsPair $ mkVarBinding ((valVar n),unitType) $ mkDummyExpr msg

-- | Single binding v<n>' = ()
mkUnitBindsPair :: Int -> BindsPair
mkUnitBindsPair n = mkSingleBindsPair $ mkVarBinding ((valVar n),unitType) $ mkUnitExpr

-- | Single binding v<n>' = defaultVal ()
mkDefaultBindsPair :: Int -> GenType -> BindsPair
mkDefaultBindsPair n t = mkSingleBindsPair $ mkVarBinding ((valVar n),t) $ mkAppExpr t "defaultVal" []

-- | Single binding v<n>' = i
mkIntLitBindsPair :: Int -> GenType -> Integer -> BindsPair
mkIntLitBindsPair n t i = mkSingleBindsPair $ mkVarBinding ((valVar n),t) $ mkIntLitExpr t i

-- | Single binding v<n>' = c
-- in C a character constant has type int!
mkCharLitBindsPair :: Int -> Char -> BindsPair
mkCharLitBindsPair n i = mkSingleBindsPair $ mkVarBinding ((valVar n),mkU32Type) $ mkCharLitExpr i

-- | Single binding v<n>' = s
mkStringLitBindsPair :: Int -> String -> BindsPair
mkStringLitBindsPair n s = mkSingleBindsPair $ mkVarBinding ((valVar n),mkStringType) $ mkStringLitExpr s

-- | Single binding v<n>' = v
mkValVarBindsPair :: Int -> TypedVar -> BindsPair
mkValVarBindsPair n v = mkSingleBindsPair $ mkVarBinding ((valVar n),snd v) $ mkVarExpr v

-- | Member (field) access <v>{f=r<k>’} = v<n>' and v<n>’ = r<k>’
--   with putback <v> = <v>{f=r<k>’}
mkMemBindsPair :: Int -> CCS.FieldName -> BindsPair -> BindsPair
mkMemBindsPair n f bp = 
    if fst rv == "_" then mainbp else addPutback (mkVarBinding rv $ mkRecPutExpr rv cmp f) mainbp
    where vv@(_,rt) = leadVar bp
          ct = getMemType f rt
          cmp = (cmpVar n, ct)
          rv = case lvalVar bp of 
                    Just v -> v
                    Nothing -> ("_",rt)
          mainbp = addBinding (mkVarBinding vv $ mkVarExpr cmp) $ 
                     addBinding (mkBinding (mkRecTakePattern rv cmp f) $ mkVarExpr vv) bp

-- | Array access (<v> @{@v<l>’=r<k>’},i<k>') = (v<n>',v<l>') and v<n>’ = r<k>’
--   with putback <v> = <v> @{@i<k>'=r<k>’}
mkIdxBindsPair :: Int -> BindsPair -> BindsPair -> BindsPair
mkIdxBindsPair n bp1 bp2 = 
    if rv == "_" then mainbp else addPutback (mkVarBinding rv $ mkArrPutExpr rv cmp idx) mainbp
    where v1@(_,at) = leadVar bp1
          v2@(_,it) = leadVar bp2
          et = getElmType at
          cmp = (cmpVar n,et)
          idx = (idxVar n,it)
          rv = case lvalVar bp1 of 
                    Just v -> v
                    Nothing -> ("_",at)
          mainbp = addBinding (mkVarBinding v1 $ mkVarExpr cmp) $ 
                     addBinding (mkBinding (mkArrTakePattern rv cmp idx v2) $ mkVarTupleExpr [v1,v2]) $ concatBindsPairs [bp2,bp1]

-- | Operator application v<n>' = op [bp...]
mkOpBindsPair :: GenType -> CCS.OpName -> [BindsPair] -> BindsPair
mkOpBindsPair t op bps =
    addBinding (mkVarBinding (fst $ head vs, t) $ mkOpExpr op (map mkVarExpr vs)) $ concatBindsPairs bps
    where vs = map leadVar bps 

-- | Function application v = f (bp...) or (v,v1,..,vn) = f (bp..,vi,..,vn)
-- The third argument is the variable to bind the function result, or the empty string if the function has result type void.
-- The fourth argument is a boolean vector marking the Add-Result arguments in bps.
-- The fifth argument is the list of additional variables for Global-State and Heap-Use arguments,
-- each with a flag whether it shall be returned as result.
mkAppBindsPair :: TypedFun -> [BindsPair] -> CCS.VarName -> [Bool] -> [(TypedVar,Bool)] -> BindsPair
mkAppBindsPair f@(_,t) bps v ars ghs =
    if any isNothing marvs
       then mkSingleBindsPair $ mkVarBinding (head rvs) $ mkDummyExpr "Unsupported Add-Result argument"
       else addBinding (mkVarsBinding rvs $ mkTypedAppExpr f [] (map mkVarExpr vs)) $ concatBindsPairs bps
    where vs = (map leadVar bps) ++ (map fst ghs)
          marvs = map lvalVar $ map snd $ filter fst $ zip ars bps
          argvs = (catMaybes marvs) ++ (map fst $ filter snd ghs)
          rvs = (if null v 
                   then if null argvs then [("_",unitType)] else []
                   else [(v,getResultType t)]) ++ argvs

-- | Assignment v<n>' = v<n>' op v<k>', (v<n>',v) = (v<n>',v<n>') or (v,v<n>')
-- The first argument is True for a postfix inc/dec operator, otherwise false.
-- The second argument is the type of the result of applying op, or the unit type if op is empty.
-- The third argument is empty for a plain assignment, otherwise the operator op to be used.
-- The fourth argument is the lvalue BindsPair.
-- The fifth argument is the operator argument BindsPair or the assigned BindsPair for a plain assignment. 
mkAssBindsPair :: Bool -> GenType -> CCS.OpName -> BindsPair -> BindsPair -> BindsPair
mkAssBindsPair post t op bpl bpr =
    case lvalVar bpl of 
         Nothing -> mkSingleBindsPair $ mkVarBinding vl $ mkDummyExpr "Unsupported lvalue in assignment"
         Just v -> let e = mkVarExpr v
                       lval = mkVarsTupleBinding [vl,v] [if post then e else el, el]
                   in addBinding lval $ addBinding (mkVarBinding vl er') $ concatBindsPairs [bpr,bpl]
    where vl = leadVar bpl
          vr = leadVar bpr
          el = mkVarExpr vl
          er = mkVarExpr vr
          er' = if null op then er else mkOpExpr t op [el,er]

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
mkVarsBinding :: [TypedVar] -> GenExpr -> GenBnd
mkVarsBinding vs e = mkTupleBinding (map mkVarPattern vs) e

-- construct v = expr
mkVarBinding :: TypedVar -> GenExpr -> GenBnd
mkVarBinding v e = mkBinding (mkVarPattern v) e

-- construct (v1,..,vn) = (e1,..,en)
mkVarsTupleBinding :: [TypedVar] -> [GenExpr] -> GenBnd
mkVarsTupleBinding [v] [e] = mkVarBinding v e
mkVarsTupleBinding vs es = mkVarsBinding vs $ mkTupleExpr es

-- replace p in (p,p1,...,pn) = expr or p = expr
replaceLeadPatn :: GenIrrefPatn -> GenBnd -> GenBnd
replaceLeadPatn ip (CS.Binding (GenIrrefPatn (CS.PTuple ps) _) _ e _) = mkTupleBinding (ip : tail ps) e
replaceLeadPatn ip' (CS.Binding ip _ e _) = mkBinding ip' e

-- | Null statement: c' = 0
mkNullBinding :: GenBnd
mkNullBinding = mkVarBinding ctlVar $ mkCtlLitExpr 0

-- | Expression statement: (c',v1..) = let ... in (0,v1..)
mkExpBinding :: BindsPair -> GenBnd
mkExpBinding bp = mkVarsBinding (typedCtlVar : vs) $ mkLetExpr [cmbBinds bp] $ mkCtlVarTupleExpr 0 vs
    where vs = sideEffectTargets bp

-- | Return statement: (c',r',v1..) = let ... in (3, v<n>',v1,..)
mkRetBinding :: BindsPair -> GenBnd
mkRetBinding bp = mkVarsBinding (typedCtlVar : ((resVar,t) : vs)) $ mkLetExpr [cmbBinds bp] $ mkCtlVarTupleExpr 3 ((v,t) : vs)
    where (v,t) = leadVar bp
          vs = sideEffectTargets bp

-- | Break statement: c' = 2
mkBreakBinding :: GenBnd
mkBreakBinding = mkVarBinding typedCtlVar $ mkCtlLitExpr 2

-- | Continue statement: c' = 1
mkContBinding :: GenBnd
mkContBinding = mkVarBinding typedCtlVar $ mkCtlLitExpr 1

-- | Conditional statement (c',z1..) = let (v<n>',v1..) = expr in if v<n>' then let b1 in (c',z1..) else let b2 in (c',z1..)
mkIfBinding :: BindsPair -> GenBnd -> GenBnd -> GenBnd
mkIfBinding bp b1 b2 =
    mkVarsBinding vs $ mkLetExpr [cmbBinds bp] $ mkIfExpr (mkVarExpr (leadVar bp)) e1 e2
    where set0 = sideEffectTargets bp
          set1 = sideEffectFilter $ boundVars b1
          set2 = sideEffectFilter $ boundVars b2
          vs = typedCtlVar : (union set0 $ union set1 set2)
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
          typedSwtVar = (swtVar,snd (leadVar bp))
          bp' = replaceLeadPatn (mkVarPattern typedSwtVar) $ cmbBinds bp
          casVars = map typedCasVar $ take (length mbps) $ iterate (1+) 1
          casVal Nothing = mkBoolLitExpr True
          casVal (Just bp) = mkBoolOpExpr "==" [mkVarExpr typedSwtVar, mkPlainExpr bp]
          mbps' = mkVarsTupleBinding casVars $ map casVal mbps
          c = mkIfExpr (mkBoolOpExpr "==" [mkVarExpr typedCtlVar,mkCtlLitExpr 2]) (mkCtlLitExpr 0) (mkVarExpr typedCtlVar)

-- | Switch group (c',x1..) = if cond then let b in (c',x1..) else (0,x1..)
mkCaseBinding :: GenBnd -> Int -> Int -> Bool -> GenBnd
mkCaseBinding b nr grps dfltSeen = 
    if dfltSeen && nr == grps
       then mkVarsBinding vs $ mkLetExpr [b] $ mkVarTupleExpr vs
       else mkVarsBinding vs $ mkIfExpr (cond dfltSeen) (mkLetExpr [b] $ mkVarTupleExpr vs) $ mk0VarTupleExpr set
    where set = sideEffectFilter $ boundVars b
          vs = typedCtlVar : set
          cond False = mkDisjExpr $ map (mkVarExpr . typedCasVar) $ take nr $ iterate (1+) 1
          cond True = mkBoolOpExpr "not" [mkDisjExpr $ map (mkVarExpr . typedCasVar) $ take (grps-nr) $ iterate (1+) (nr+1)]

-- | Statement in Sequence (c',z1..) = let b in if c' > 0 then (c',z1..) else let bs in (c',z1..)
mkSeqBinding :: GenBnd -> GenBnd -> GenBnd
mkSeqBinding b bs =
    mkVarsBinding vs $ mkLetExpr [b] $ 
      mkIfExpr (mkBoolOpExpr ">" [mkVarExpr typedCtlVar,mkCtlLitExpr 0]) e $ mkLetExpr [bs] $ e
    where set1 = sideEffectFilter $ boundVars b
          set2 = sideEffectFilter $ boundVars bs
          vs = typedCtlVar : (union set1 set2)
          e = mkVarTupleExpr vs

-- | Jump-free statement in sequence (c’,z1..) = let b and bs in (c’,z1..)
mkSimpSeqBinding :: GenBnd -> GenBnd -> GenBnd
mkSimpSeqBinding b bs =
    mkVarsBinding vs $ mkLetExpr [b, bs] $ mkVarTupleExpr vs
    where set1 = sideEffectFilter $ boundVars b
          set2 = sideEffectFilter $ boundVars bs
          vs = typedCtlVar : (union set1 set2)

-- | Declarator in Sequence 
-- (c’,z1..) = let (v<n>’,v1..) = expr and (c’,u1..) = let v = v<n>’ and b in (c’,u1..) in (c’,z1..)
mkDecBinding :: TypedVar -> BindsPair -> GenBnd -> GenBnd
mkDecBinding v bp b = 
    mkVarsBinding vs $ mkLetExpr [cmbBinds bp, mkVarsBinding vs' e] $ mkVarTupleExpr vs
    where setv = sideEffectTargets bp
          sety = sideEffectFilter $ boundVars b
          setu = delete v sety
          setz = union setv setu
          vs = typedCtlVar : setz
          vs' = typedCtlVar : setu
          e = mkLetExpr [mkVarBinding v $ mkVarExpr $ leadVar bp, b] $ mkVarTupleExpr vs'

-- | Declaration as sequence of declarators
mkDeclBinding :: [(TypedVar,BindsPair)] -> GenBnd -> GenBnd
mkDeclBinding [] b = b
mkDeclBinding ((v,bp) : ds) b = mkDecBinding v bp $ mkDeclBinding ds b

-- | for statement: 
mkForBinding :: BindsPair -> (Either (Maybe BindsPair) [(TypedVar,BindsPair)]) -> BindsPair -> BindsPair -> GenBnd -> GenBnd
mkForBinding bpm ebp1 bp2 bp3 b = 
    case ebp1 of
         (Left Nothing) -> bindloop
         (Left (Just bp1)) -> mkSimpSeqBinding (cmbBinds bp1) bindloop
         (Right ds) -> mkDeclBinding ds bindloop
    where b3 = cmbBinds bp3
          accvars = union (sideEffectFilter $ boundVars b) (sideEffectFilter $ boundVars b3)
          exprstep = mkLetExpr [b] $ mkIfExpr ctlcond accexpr $ mkLetExpr [b3] $ mk0VarTupleExpr accvars
          b2@(CS.Binding _ _ expr2 _) = cmbBinds bp2
          freevars = union (getFreeTypedVars exprstep) (getFreeTypedVars expr2)
          exprloop = mkLetExpr [(mkBinding accpat $ mkAppExpr "repeat" [repeatargexpr])] $ mkExpVarTupleExpr repeatctl accvars
          accpat = mkPatVarTuplePattern mkCtrlPattern accvars -- (c',y1..)
          accexpr = mkVarTupleExpr (typedCtlVar : accvars) -- (c',y1..)
          ctlcond = mkBoolOpExpr ">" [mkVarExpr typedCtlVar,mkCtlLitExpr 1] -- c' > 1
          accpatwild = mkPatVarTuplePattern mkWildcardPattern accvars -- (_,y1..)
          obsvars = freevars \\ accvars
          obsvpat = mkVarTuplePattern obsvars
          repeatctl = mkIfExpr (mkBoolOpExpr "==" [mkVarExpr typedCtlVar,mkCtlLitExpr 2]) (mkCtlLitExpr 0) (mkVarExpr typedCtlVar)
          repeatargexpr = mkRecordExpr [("n",exprmax),("stop",stopfun),("step",stepfun),("acc",iniacc),("obsv",iniobsv)]
          exprmax = mkPlainExpr bpm
          iniacc = mk0VarTupleExpr accvars
          iniobsv = mkVarTupleExpr obsvars
          stopfun = mkLambdaExpr (mkRecordPattern [("acc",accpat),("obsv",obsvpat)]) $ mkLetExpr [b2] stopexpr
          stopexpr = mkDisjExpr [ctlcond, mkBoolOpExpr "not" [mkVarExpr $ leadVar bp2]]
          stepfun = mkLambdaExpr (mkRecordPattern [("acc",accpatwild),("obsv",obsvpat)]) exprstep
          bindloop = mkBinding accpat exprloop

-- | Combine all bindings in a binding list pair to a single binding.
-- (v<n>',v1..) = let ... in (v<n>',v1..)
cmbBinds :: BindsPair -> GenBnd
cmbBinds bp = cmbExtBinds (sideEffectTargets bp) bp

-- | Combine all bindings in a binding list pair to a single binding with given side effect targets.
cmbExtBinds :: [TypedVar] -> BindsPair -> GenBnd
cmbExtBinds vs bp@(main,putback) = 
    mkVarsBinding vs' $ mkLetExpr bs $ mkVarTupleExpr vs'
    where lv = leadVar bp
          vs' = if elem lv vs then vs else lv : vs
          bs = (reverse main) ++ putback

-- Construct Patterns
---------------------

genIrrefPatn t p = GenIrrefPatn p noOrigin t

mkWildcardPattern :: GenType -> GenIrrefPatn
mkWildcardPattern t = genIrrefPatn t CS.PUnderscore

mkVarPattern :: TypedVar -> GenIrrefPatn
mkVarPattern (v,t) = genIrrefPatn t $ CS.PVar v

mkCtrlPattern :: GenIrrefPatn
mkCtrlPattern = mkVarPattern (ctlVar,mkCtlType)

mkValPattern :: GenType -> Int -> GenIrrefPatn
mkValPattern t i = mkVarPattern (valVar i,t)

mkTuplePattern :: [GenIrrefPatn] -> GenIrrefPatn
mkTuplePattern [ip] = ip
mkTuplePattern ips = genIrrefPatn (mkTupleType (map typOfGIP ips)) $ CS.PTuple ips

-- construct (v1,..,vn)
mkVarTuplePattern :: [TypedVar] -> GenIrrefPatn
mkVarTuplePattern vs = mkTuplePattern $ map mkVarPattern vs

-- construct (p,v1,..,vn)
mkPatVarTuplePattern :: GenIrrefPatn -> [TypedVar] -> GenIrrefPatn
mkPatVarTuplePattern p vs = mkTuplePattern (p : map mkVarPattern vs)

-- construct #{f1 = p1, ..., fn = pn}
mkRecordPattern :: [(CCS.FieldName,GenIrrefPatn)] -> GenIrrefPatn
mkRecordPattern flds = genIrrefPatn (mkRecordType (map (\(f,ip) -> (f,typOfGIP ip)) flds) $ CS.PUnboxedRecord $ map Just flds

-- construct v1{m=v2}
mkRecTakePattern :: TypedVar -> TypedVar -> CCS.FieldName -> GenIrrefPatn
mkRecTakePattern tv1@(v1,t1) tv2 m = genIrrefPatn (mkTakeType False t1 [f]) $ CS.PTake v1 [Just (m, mkVarPattern tv2)]

-- construct (v1 @{@v4=v2},v3)
mkArrTakePattern :: TypedVar -> TypedVar -> TypedVar -> TypedVar -> GenIrrefPatn
mkArrTakePattern tv1@(v1,t1) tv2 tv3 tv4 = 
    mkTuplePattern [genIrrefPatn (mkArrTakeType False t1 [ip3]) $ CS.PArrayTake v1 [(mkVarExpr tv4,mkVarPattern tv2)], ip3]
    where ip3 = mkVarPattern tv3

