{-# LANGUAGE PackageImports #-}
module Gencot.Cogent.Bindings where

import Data.List (union,nub,delete,(\\))
import Data.Maybe (catMaybes,isNothing)

import Cogent.Surface as CS
import Cogent.Common.Syntax as CCS

import Gencot.Origin (noOrigin)
import Gencot.Names (ptrDerivCompName)
import Gencot.Cogent.Ast -- includes unitType
import Gencot.Cogent.Types (
  mkU8Type, mkU32Type, mkStringType, mkBoolType, 
  mkTupleType, mkCtlType, mkFunType, mkRecordType, mkTakeType, mkArrTakeType, 
  getMemberType, getDerefType, transferProperties)
import Gencot.Cogent.Expr (
  TypedVar(TV), namOfTV, typOfTV, TypedVarOrWild, TypedFun, funResultType,
  mkUnitExpr, mkIntLitExpr, mkCharLitExpr, mkStringLitExpr, mkBoolLitExpr,
  mkVarExpr, mkFunExpr, mkCtlLitExpr, mkTupleExpr, mkOpExpr, mkBoolOpExpr, mkCtlVarTupleExpr, mkVarTupleExpr, mkExpVarTupleExpr, mk0VarTupleExpr,
  mkDisjExpr, mkAppExpr, mkTopLevelFunExpr, mkLetExpr, mkRecPutExpr, mkArrPutExpr,
  mkIfExpr, mkRecordExpr, mkLambdaExpr,
  getFreeTypedVars)

prime = '\''

ctlVar = "c"++[prime]

resVar = "r"++[prime]

swtVar = "s"++[prime]

errVar = "err"++[prime]

casVar :: Int -> CCS.VarName
casVar n = "s"++(show n)++[prime]

cmpVar :: Int -> CCS.VarName
cmpVar n = "p"++(show n)++[prime]

idxVar :: Int -> CCS.VarName
idxVar n = "i"++(show n)++[prime]

valVar :: Int -> CCS.VarName
valVar 0 = "v"++[prime]
valVar n = "v"++(show n)++[prime]

typedCtlVar = TV ctlVar mkCtlType
typedCasVar n = TV (casVar n) mkBoolType

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
sideEffectTargets :: BindsPair -> [TypedVarOrWild]
sideEffectTargets (main,putback) =
    sideEffectFilter $ union (boundVarsList main) (boundVarsList putback)

-- | Select side effect targets from a list of typed variables.
sideEffectFilter :: [TypedVarOrWild] -> [TypedVarOrWild]
sideEffectFilter vs =
    filter (\(TV v _) -> (last v) /= prime || v == resVar) vs

-- | All typed variables occurring in a pattern.
tupleVars :: GenIrrefPatn -> [TypedVarOrWild]
tupleVars ip =
    case irpatnOfGIP ip of
         CS.PVar v -> [TV v $ typOfGIP ip]
         CS.PUnderscore -> [TV "_" $ typOfGIP ip]
         CS.PTuple pvs -> concat $ map tupleVars pvs
         CS.PTake v fs -> (TV v $ mkTakeType False (typOfGIP ip) (map fst $ catMaybes fs)) : (concat $ map (tupleVars . snd) $ catMaybes fs)
         CS.PArrayTake v fs -> (TV v $ mkArrTakeType False (typOfGIP ip) (map fst fs)) : (concat $ map (tupleVars . snd) fs)

-- | Typed variables bound in a binding
-- For a valid binding all resulting variables have different names.
boundVars :: GenBnd -> [TypedVarOrWild]
boundVars (CS.Binding ip _ _ _) = tupleVars ip

-- | Typed variables bound in a binding list
-- The result may contain variables with the same name but different types.
boundVarsList :: [GenBnd] -> [TypedVarOrWild]
boundVarsList bs = nub $ concat $ map boundVars bs

-- | The first typed variable bound in the final binding of the main list.
leadVar :: BindsPair -> TypedVarOrWild
leadVar (main,_) = head $ tupleVars ip
    where (CS.Binding ip _ _ _) = head main

isStatBindsPair :: BindsPair -> Bool
isStatBindsPair bp = (namOfTV (leadVar bp)) == ctlVar

boundExpr :: GenBnd -> GenExpr
boundExpr (CS.Binding _ _ e _) = e

isWild :: TypedVarOrWild -> Bool
isWild (TV "_" _) = True
isWild _ = False

-- | The first expression bound in the final binding of the main list, if it is a variable.
lvalVar :: BindsPair -> TypedVarOrWild
lvalVar (main,_) = 
    case exprOfGE e of
         (CS.Tuple es) -> 
            case exprOfGE $ head es of
                 (CS.Var v) -> (TV v $ typOfGE $ head es)
                 _ -> (TV errVar $ typOfGE $ head es)
         (CS.Var v) -> (TV v $ typOfGE e)
         _ -> (TV errVar $ typOfGE e)
    where (CS.Binding _ _ e _) = head main

replaceValVarType :: GenType -> GenIrrefPatn -> [GenBnd] -> [GenBnd]
-- TODO
replaceValVarType t ip bs = bs

-- Construct Toplevel Expressions
---------------------------------

-- construct let (_,...) = expr in e
mkBodyExpr :: GenBnd -> GenExpr -> GenExpr
mkBodyExpr b@(CS.Binding ip _ _ _) e = mkLetExpr [replaceLeadPatn (mkVarPattern (TV "_" $ typOfGIP ip)) b] e

-- construct let ... in v<n>'
mkPlainExpr :: ([GenBnd],[GenBnd]) {-BindsPair-} -> GenExpr
mkPlainExpr (main,putback) =
    if not $ null putback
       then toDummyExpr e $ mkDummyExpr unitType "No putback obligations supported in plain expression."
       else
       if (length vs) > 1
          then toDummyExpr e $ mkDummyExpr unitType "No side effects supported in plain expression."
          else mkLetExpr (reverse main) $ mkVarExpr $ head vs
    where (CS.Binding ip _ e _) = head main
          vs = tupleVars ip

-- construct (gencotDummy msg)
-- use mkVarExpr instead of mkTopLevelFunExpr to omit type and layout arguments
mkDummyExpr :: GenType -> String -> GenExpr
mkDummyExpr t msg = mkAppExpr (mkVarExpr (TV "gencotDummy" $ mkFunType mkStringType t)) $ mkStringLitExpr msg

-- turn expression to dummy, preserving origin, type, and source
toDummyExpr :: GenExpr -> GenExpr -> GenExpr
toDummyExpr (GenExpr e o t src) (GenExpr dummy _ _ _) = (GenExpr dummy o t src)

-- Construct Binding List Pairs
-------------------------------

mkEmptyBindsPair :: BindsPair
mkEmptyBindsPair = ([],[])

-- | Construct a binding list pair from a single binding.
mkSingleBindsPair :: GenBnd -> BindsPair
mkSingleBindsPair b = ([b],[])

-- | Single binding v<n>' = gencotDummy msg
mkDummyBindsPair :: Int -> GenType -> String -> BindsPair
mkDummyBindsPair n t msg = mkSingleBindsPair $ mkValVarBinding n t $ mkDummyExpr t msg

-- | Single binding v<n>' = ()
mkUnitBindsPair :: Int -> BindsPair
mkUnitBindsPair n = mkSingleBindsPair $ mkValVarBinding n unitType $ mkUnitExpr

-- | Single binding v<n>' = defaultVal ()
mkDefaultBindsPair :: Int -> GenType -> BindsPair
mkDefaultBindsPair n t =
    mkSingleBindsPair $ mkValVarBinding n t $ mkAppExpr (mkTopLevelFunExpr ("defaultVal",mkFunType unitType t) [Just t]) mkUnitExpr

-- | Single binding v<n>' = i
mkIntLitBindsPair :: Int -> GenType -> Integer -> BindsPair
mkIntLitBindsPair n t i = mkSingleBindsPair $ mkValVarBinding n t $ mkIntLitExpr t i

-- | Single binding v<n>' = c
-- in C a character constant has type int!
mkCharLitBindsPair :: Int -> Char -> BindsPair
mkCharLitBindsPair n i = mkSingleBindsPair $ mkValVarBinding n mkU32Type $ mkCharLitExpr i

-- | Single binding v<n>' = s
mkStringLitBindsPair :: Int -> String -> BindsPair
mkStringLitBindsPair n s = mkSingleBindsPair $ mkValVarBinding n mkStringType $ mkStringLitExpr s

-- | Single binding v<n>' = v
mkValVarBindsPair :: Int -> TypedVar -> BindsPair
mkValVarBindsPair n v = mkSingleBindsPair $ mkValVarBinding n (typOfTV v) $ mkVarExpr v

-- | Member (field) access <v>{f=r<k>’} = v<n>' and v<n>’ = r<k>’
--   with putback <v> = <v>{f=r<k>’}
mkMemBindsPair :: Int -> CCS.FieldName -> BindsPair -> BindsPair
mkMemBindsPair n f bp = 
    if isWild rv then mainbp else addPutback (mkVarBinding rv $ mkRecPutExpr rv cmp f) mainbp
    where vv@(TV _ rt) = leadVar bp
          ct = getMemberType f rt
          cmp = TV (cmpVar n) ct
          rv = lvalVar bp
          mainbp = addBinding (mkVarBinding vv $ mkVarExpr cmp) $ 
                     addBinding (mkBinding (mkRecTakePattern rv cmp f) $ mkVarExpr vv) bp

-- | Array access (<v> @{@v<l>’=r<k>’},i<k>') = (v<n>',v<l>') and v<n>’ = r<k>’
--   with putback <v> = <v> @{@i<k>'=r<k>’}
mkIdxBindsPair :: Int -> BindsPair -> BindsPair -> BindsPair
mkIdxBindsPair n bp1 bp2 = 
    if isWild rv then mainbp else addPutback (mkVarBinding rv $ mkArrPutExpr rv cmp idx) mainbp
    where v1@(TV _ at) = leadVar bp1
          v2@(TV _ it) = leadVar bp2
          et = getDerefType at
          cmp = TV (cmpVar n) et
          idx = TV (idxVar n) it
          rv = lvalVar bp1
          mainbp = addBinding (mkVarBinding v1 $ mkVarExpr cmp) $ 
                     addBinding (mkBinding (mkArrTakePattern rv cmp idx v2) $ mkVarTupleExpr [v1,v2]) $ concatBindsPairs [bp2,bp1]

-- | Pointer dereference, always <v>{cont=r<k>’} = v<n>' and v<n>’ = r<k>’
--   with putback <v> = <v>{cont=r<k>’}
-- The type of v<n>' may be an arbitrary mapped C pointer type except function pointer type.
mkDerefBindsPair :: Int -> BindsPair -> BindsPair
mkDerefBindsPair n bp =
    if isWild rv then mainbp else addPutback (mkVarBinding rv $ mkRecPutExpr rv cmp f) mainbp
    where f = ptrDerivCompName
          vv@(TV _ rt) = leadVar bp
          ct = getDerefType rt
          cmp = TV (cmpVar n) ct
          rv = lvalVar bp
          mainbp = addBinding (mkVarBinding vv $ mkVarExpr cmp) $
                     addBinding (mkBinding (mkRecTakePattern rv cmp f) $ mkVarExpr vv) bp

-- | Operator application v<n>' = op [bp...]
mkOpBindsPair :: GenType -> CCS.OpName -> [BindsPair] -> BindsPair
mkOpBindsPair t op bps =
    addBinding (mkVarBinding (TV (namOfTV $ head vs) t) $ mkOpExpr t op (map mkVarExpr vs)) $ concatBindsPairs bps
    where vs = map leadVar bps 

-- | Application of constant named function v<n>' = f ()
mkConstAppBindsPair :: Int -> TypedFun -> BindsPair
mkConstAppBindsPair n f = mkSingleBindsPair $ mkValVarBinding n (funResultType f) $ mkAppExpr (mkFunExpr f) mkUnitExpr

-- | Function pointer dereference f = fromFunPtr (fp)
-- The first argument is the type of the resulting function.
mkFunDerefBindsPair :: GenType -> BindsPair -> BindsPair
mkFunDerefBindsPair ft bp =
    addBinding (mkVarBinding (TV vnam ft) $ mkAppExpr (mkTopLevelFunExpr ("fromFunPtr",ffpt) [Just ft, Just fpt]) (mkVarExpr v)) bp
    where v@(TV vnam fpt) = leadVar bp
          ffpt = mkFunType fpt ft

-- | Function application v = f (pbp) or (v,v1,..,vn) = f (pbp)
-- The first argument is the BindsPair for the function
-- The second argument is the pattern for binding the function result
-- The third argument is the list of BindsPairs for the parameter tuple (or single parameter or unit value)
mkAppBindsPair :: BindsPair -> GenIrrefPatn -> [BindsPair] -> BindsPair
mkAppBindsPair fbp rpat pbps =
    addBinding (mkBinding rpat $ mkAppExpr (mkVarExpr $ leadVar fbp) (mkTupleExpr (map (mkVarExpr . leadVar) pbps))) $ concatBindsPairs (fbp : pbps)

-- | Assignment v<n>' = v<n>' op v<k>', (v<n>',v) = (v<n>',v<n>') or (v,v<n>')
-- The first argument is True for a postfix inc/dec operator, otherwise false.
-- The second argument is the type of the result of applying op, or the unit type if op is empty.
-- The third argument is empty for a plain assignment, otherwise the operator op to be used.
-- The fourth argument is the lvalue BindsPair.
-- The fifth argument is the operator argument BindsPair or the assigned BindsPair for a plain assignment. 
mkAssBindsPair :: Bool -> GenType -> CCS.OpName -> BindsPair -> BindsPair -> BindsPair
mkAssBindsPair post t op bpl bpr =
    addBinding lval $ addBinding (mkVarBinding vl er') $ concatBindsPairs [bpr,bpl]
    where vl = leadVar bpl
          vr = leadVar bpr
          el = mkVarExpr vl
          er = mkVarExpr vr
          er' = if null op then er else mkOpExpr t op [el,er]
          v = lvalVar bpl
          e = mkVarExpr v
          lval = mkVarsTupleBinding [vl,v] [if post then e else el, el]

-- | Conditional v<n>' = if bp1 then bp2 else bp3
-- The first argument is the result type but without the effect of properties,
-- these are taken from bp1, assuming that they are the same in bp2.
mkIfBindsPair :: GenType -> BindsPair -> BindsPair -> BindsPair -> BindsPair
mkIfBindsPair t bp0 bp1 bp2 =
    addBinding (mkVarsBinding (vr : set) (mkIfExpr (mkVarExpr v0) e1 e2)) bp
    where set1 = sideEffectTargets bp1
          set2 = sideEffectTargets bp2
          v0 = leadVar bp0
          v1 = leadVar bp1
          v2 = leadVar bp2
          vr = TV (namOfTV v0) (transferProperties (typOfTV v1) t)
          set = union set1 set2
          (bp1l,e1) = if null set1
                         then ([bp1],mkVarTupleExpr (v1 : set))
                         else ([],boundExpr $ cmbExtBinds set bp1)
          (bp2l,e2) = if null set2
                         then ([bp2],mkVarTupleExpr (v2 : set))
                         else ([],boundExpr $ cmbExtBinds set bp2)
          bp = concatBindsPairs (bp0 : (bp1l ++ bp2l))

-- | Tuple expression v<n>' = (bp1,...,bpk)
-- Value variable v<n>' is taken from bp1.
-- If k=0 then <n> must be provided as first argument.
mkTupleBindsPair :: Int -> [BindsPair] -> BindsPair
mkTupleBindsPair n [] = mkUnitBindsPair n
mkTupleBindsPair _ [bp] = bp
mkTupleBindsPair _ bps = 
    addBinding (mkVarBinding (leadVar $ head bps) $ mkTupleExpr (map (mkVarExpr . leadVar) bps)) $ concatBindsPairs bps

-- | Replace the type in the leading value variable of a pattern by a given type.
-- The pattern must be a single variable or wildcard or a tuple with a variable or wildcard as first component.
replaceBoundVarType :: GenType -> BindsPair -> BindsPair 
replaceBoundVarType t ((CS.Binding ip mt e vs) : mtl, putback) =
    ((CS.Binding (replaceInGIP t ip) mt e vs) : mtl, putback)

replaceInGIP :: GenType -> GenIrrefPatn -> GenIrrefPatn
replaceInGIP t (GenIrrefPatn (CS.PVar v) o _) = (GenIrrefPatn (CS.PVar v) o t)
replaceInGIP t (GenIrrefPatn CS.PUnderscore o _) = (GenIrrefPatn CS.PUnderscore o t)
replaceInGIP t (GenIrrefPatn (CS.PTuple pvs) o (GenType (CS.TTuple ts) ot _)) =
    (GenIrrefPatn (CS.PTuple pvs') o (GenType (CS.TTuple ts') ot Nothing))
    where ip' = (replaceInGIP t $ head pvs)
          pvs' = ip' : (tail pvs)
          ts' = (typOfGIP ip') : (tail ts)

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
mkDummyBinding msg = mkVarBinding typedCtlVar $ mkDummyExpr mkCtlType msg

-- construct (p1,..,pn) = expr or p1 = expr
mkTupleBinding :: [GenIrrefPatn] -> GenExpr -> GenBnd
mkTupleBinding ps e = mkBinding (mkTuplePattern ps) e

-- construct (v1,..,vn) = expr or v1 = expr
mkVarsBinding :: [TypedVarOrWild] -> GenExpr -> GenBnd
mkVarsBinding vs e = mkTupleBinding (map mkVarPattern vs) e

-- construct v = expr
mkVarBinding :: TypedVarOrWild -> GenExpr -> GenBnd
mkVarBinding v e = mkBinding (mkVarPattern v) e

-- construct v<n>' = expr
mkValVarBinding :: Int -> GenType -> GenExpr -> GenBnd
mkValVarBinding n t e = mkBinding (mkValVarPattern n t) e

-- construct (v1,..,vn) = (e1,..,en)
mkVarsTupleBinding :: [TypedVarOrWild] -> [GenExpr] -> GenBnd
mkVarsTupleBinding [v] [e] = mkVarBinding v e
mkVarsTupleBinding vs es = mkVarsBinding vs $ mkTupleExpr es

-- replace p in (p,p1,...,pn) = expr or p = expr
replaceLeadPatn :: GenIrrefPatn -> GenBnd -> GenBnd
replaceLeadPatn ip (CS.Binding (GenIrrefPatn (CS.PTuple ps) _ _) _ e _) = mkTupleBinding (ip : tail ps) e
replaceLeadPatn ip' (CS.Binding ip _ e _) = mkBinding ip' e

-- | Null statement: c' = 0
mkNullBinding :: GenBnd
mkNullBinding = mkVarBinding typedCtlVar $ mkCtlLitExpr 0

-- | Expression statement: (c',v1..) = let ... in (0,v1..)
mkExpBinding :: BindsPair -> GenBnd
mkExpBinding bp = mkVarsBinding (typedCtlVar : vs) $ mkLetExpr [cmbBinds bp] $ mkCtlVarTupleExpr 0 vs
    where vs = sideEffectTargets bp

-- | Return statement: (c',r',v1..) = let ... in (3, v<n>',v1,..)
-- Second argument is the result type of the enclosing function.
mkRetBinding :: GenType -> BindsPair -> GenBnd
mkRetBinding t bp = mkVarsBinding (typedCtlVar : ((TV resVar t) : vs)) $ mkLetExpr [cmbBinds bp] $ mkCtlVarTupleExpr 3 (v : vs)
    where v = leadVar bp
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
    mkVarsBinding (typedCtlVar : vs) $ mkLetExpr [bp',mbps',b] $ mkExpVarTupleExpr c vs
    where set0 = sideEffectTargets bp
          set1 = sideEffectFilter $ boundVars b
          vs = union set0 set1
          typedSwtVar = TV swtVar $ typOfTV $ leadVar bp
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
          accpat = mkVarTuplePattern (typedCtlVar : accvars) -- (c',y1..)
          accexpr = mkVarTupleExpr (typedCtlVar : accvars) -- (c',y1..)
          ctlcond = mkBoolOpExpr ">" [mkVarExpr typedCtlVar,mkCtlLitExpr 1] -- c' > 1
          accpatwild = mkVarTuplePattern ((TV "_" mkCtlType) : accvars) -- (_,y1..)
          obsvars = freevars \\ accvars
          obsvpat = mkVarTuplePattern obsvars
          repeatctl = mkIfExpr (mkBoolOpExpr "==" [mkVarExpr typedCtlVar,mkCtlLitExpr 2]) (mkCtlLitExpr 0) (mkVarExpr typedCtlVar)
          repeatargexpr = mkRecordExpr [("n",exprmax),("stop",stopfun),("step",stepfun),("acc",iniacc),("obsv",iniobsv)]
          exprmax = mkPlainExpr bpm
          iniacc = mk0VarTupleExpr accvars
          iniobsv = mkVarTupleExpr obsvars
          repeattype = mkFunType (typOfGE repeatargexpr) (typOfGE iniacc)
          repeatfun = mkTopLevelFunExpr ("repeat",repeattype) [Just $ typOfGE iniacc, Just $ typOfGE iniobsv]
          exprloop = mkLetExpr [(mkBinding accpat $ mkAppExpr repeatfun repeatargexpr)] $ mkExpVarTupleExpr repeatctl accvars
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

mkVarPattern :: TypedVarOrWild -> GenIrrefPatn
mkVarPattern v = genIrrefPatn (typOfTV v) $ (if isWild v then CS.PUnderscore else CS.PVar (namOfTV v))

mkValVarPattern :: Int -> GenType -> GenIrrefPatn
mkValVarPattern n t = mkVarPattern $ TV (valVar n) t

mkTuplePattern :: [GenIrrefPatn] -> GenIrrefPatn
mkTuplePattern [] = genIrrefPatn unitType $ CS.PUnitel
mkTuplePattern [ip] = ip
mkTuplePattern ips = genIrrefPatn (mkTupleType (map typOfGIP ips)) $ CS.PTuple ips

-- construct (v1,..,vn)
mkVarTuplePattern :: [TypedVarOrWild] -> GenIrrefPatn
mkVarTuplePattern vs = mkTuplePattern $ map mkVarPattern vs

-- construct #{f1 = p1, ..., fn = pn}
mkRecordPattern :: [(CCS.FieldName,GenIrrefPatn)] -> GenIrrefPatn
mkRecordPattern flds = genIrrefPatn (mkRecordType (map (\(f,ip) -> (f,typOfGIP ip)) flds)) $ CS.PUnboxedRecord $ map Just flds

-- construct v1{f=v2}
mkRecTakePattern :: TypedVarOrWild -> TypedVarOrWild -> CCS.FieldName -> GenIrrefPatn
mkRecTakePattern tv1@(TV v1 t1) tv2 f = genIrrefPatn (mkTakeType False t1 [f]) $ CS.PTake v1 [Just (f, mkVarPattern tv2)]

-- construct (v1 @{@v4=v2},v3)
mkArrTakePattern :: TypedVarOrWild -> TypedVarOrWild -> TypedVarOrWild -> TypedVar -> GenIrrefPatn
mkArrTakePattern tv1@(TV v1 t1) tv2 tv3 tv4 =
    mkTuplePattern [genIrrefPatn (mkArrTakeType False t1 [ie3]) $ CS.PArrayTake v1 [(mkVarExpr tv4,mkVarPattern tv2)], ip3]
    where ip3 = mkVarPattern tv3
          ie3 = mkVarExpr tv3

-- Construct Alternative
------------------------

mkAlt :: GenIrrefPatn -> GenExpr -> GenAlt
mkAlt p e = CS.Alt (GenPatn (CS.PIrrefutable p) noOrigin $ typOfGIP p) CCS.Regular e

-- Handling mf flags
--------------------
{- Currently not used -}

-- Reorganise BindsPairs according to mf flags, if necessary
-- First argument is value variable index for second parameter if only one parameter exists and has an mf flag.
processMFpropForBindsPairs :: Int -> [(BindsPair, Bool)] -> [BindsPair]
processMFpropForBindsPairs n mfbps =
    if null postmf
       then map fst premf
       else [fst $ head postmf, mkTupleBindsPair n $ map fst (premf ++ (tail postmf))]
    where (premf,postmf) = break snd $ mfbps

-- Reorganise variables according to mf flags, if necessary, and convert to patterns
-- If there is an mf flag, the result always has two patterns, one for the first variable with mf flag
-- and one for the tuple of other variables, or the wildcard pattern if there are no others.
processMFpropForPatterns :: [(TypedVarOrWild, Bool)] -> [GenIrrefPatn]
processMFpropForPatterns mfvars =
    if null postmf
       then map fst premf
       else [fst $ head postmf, arpat]
    where (premf,postmf) = break snd $ map (\(tv,mf) -> (mkVarPattern tv, mf)) mfvars
          arpats = map fst (premf ++ (tail postmf))
          arpat = if null arpats then mkVarPattern (TV "_" unitType) else mkTuplePattern arpats
