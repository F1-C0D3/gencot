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
  getMemberType, getDerefType, adaptTypes)
import Gencot.Cogent.Expr (
  TypedVar(TV), namOfTV, typOfTV, TypedFun, funResultType,
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

-- A translated C expression.
-- It consists of a list of bindings and two variables.
-- The first variable is bound to the result value after applying the bindings in the list.
-- The second variable corresponds to the expression if interpreted as lvalue.
-- If it is Nothing the expression cannot be used as lvalue.
type ExprBinds = ([GenBnd],(TypedVar, Maybe TypedVar))

binds :: ExprBinds -> [GenBnd]
binds (bs, _) = bs

-- | The variable bound to the result value.
leadVar :: ExprBinds -> TypedVar
leadVar (_,(tv,_)) = tv

-- | The variable representing the lvalue.
-- If not available the error variable with unit type is returned.
lvalVar :: ExprBinds -> TypedVar
lvalVar (_,(_,Nothing)) = TV errVar unitType
lvalVar (_,(_,Just tv)) = tv

-- | Select side effect targets from a binding list pair.
-- For every variable name its last occurrence as bound variable in the sequence of bindings is returned.
-- This is the binding effective at the end of the binding sequence with its associated type.
-- Note that a container variable may have several different types with taken components in the binding sequence.
sideEffectTargets :: ExprBinds -> [TypedVar]
sideEffectTargets bp =
    sideEffectFilter $ boundVarsList $ binds bp

-- | Select side effect targets from a list of typed variables.
sideEffectFilter :: [TypedVar] -> [TypedVar]
sideEffectFilter vs =
    filter (\(TV v _) -> (last v) /= prime || v == resVar) vs

-- | All typed variables occurring in a pattern.
tupleVars :: GenIrrefPatn -> [TypedVar]
tupleVars ip =
    case irpatnOfGIP ip of
         CS.PVar v -> [TV v $ typOfGIP ip]
         CS.PUnderscore -> [TV "_" $ typOfGIP ip]
         CS.PUnitel -> []
         CS.PTuple pvs -> concat $ map tupleVars pvs
         CS.PTake v fs -> (TV v $ typOfGIP ip) : (concat $ map (tupleVars . snd) $ catMaybes fs)
         CS.PArrayTake v fs -> (TV v $ typOfGIP ip) : (concat $ map (tupleVars . snd) fs)

-- | Typed variables bound in a binding
-- For a valid binding all resulting variables have different names.
boundVars :: GenBnd -> [TypedVar]
boundVars (CS.Binding ip _ _ _) = tupleVars ip

-- | Typed variables bound in a binding list
-- The result may contains for each variable name only the first occurrence with its associated type.
boundVarsList :: [GenBnd] -> [TypedVar]
boundVarsList bs = nub $ concat $ map boundVars bs -- nub always retains the first occurrence

boundExpr :: GenBnd -> GenExpr
boundExpr (CS.Binding _ _ e _) = e

isErrVar :: TypedVar -> Bool
isErrVar (TV nam _) = nam == errVar

-- | Retrieve the lvalue variable from an expression, if available.
-- It is the variable bound as expression in the first component, if that is a variable.
lvalVarInExpr :: GenExpr -> Maybe TypedVar
lvalVarInExpr (GenExpr (CS.Tuple es) _ _ _) = lvalVarInExpr $ head es
lvalVarInExpr (GenExpr (CS.Var v) _ t _) = Just $ TV v t
lvalVarInExpr _ = Nothing

-- Construct Toplevel Expressions
---------------------------------

-- construct let ... in v<n>'
mkPlainExpr :: ExprBinds -> GenExpr
mkPlainExpr bp =
    if (length vs) > 1
       then toDummyExpr e $ mkDummyExpr (typOfGE e) "No side effects supported in plain expression."
       else e
    where b@(CS.Binding ip _ e _) = cmbBinds bp
          vs = tupleVars ip

-- construct (gencotDummy msg)
-- use mkVarExpr instead of mkTopLevelFunExpr to omit type and layout arguments
mkDummyExpr :: GenType -> String -> GenExpr
mkDummyExpr t msg = mkAppExpr (mkVarExpr (TV "gencotDummy" $ mkFunType mkStringType t)) $ mkStringLitExpr msg

-- turn expression to dummy, preserving origin and source
toDummyExpr :: GenExpr -> GenExpr -> GenExpr
toDummyExpr (GenExpr _ o _ src) (GenExpr dummy _ t _) = (GenExpr dummy o t src)

-- Construct Binding List Pairs
-------------------------------

mkEmptyExprBinds :: ExprBinds
mkEmptyExprBinds = ([],(TV errVar unitType, Nothing))

-- | Construct a binding list pair from a single binding.
mkSingleExprBinds :: GenBnd -> ExprBinds
mkSingleExprBinds b = ([b],(head $ boundVars b, lvalVarInExpr $ boundExpr b))

-- | Single binding v<n>' = gencotDummy msg
mkDummyExprBinds :: Int -> GenType -> String -> ExprBinds
mkDummyExprBinds n t msg = mkSingleExprBinds $ mkValVarBinding n t $ mkDummyExpr t msg

-- | Single binding v<n>' = ()
mkUnitExprBinds :: Int -> ExprBinds
mkUnitExprBinds n = mkSingleExprBinds $ mkValVarBinding n unitType $ mkUnitExpr

-- | Single binding v<n>' = defaultVal ()
mkDefaultExprBinds :: Int -> GenType -> ExprBinds
mkDefaultExprBinds n t =
    mkSingleExprBinds $ mkValVarBinding n t $ mkAppExpr (mkTopLevelFunExpr ("defaultVal",mkFunType unitType t) [Just t]) mkUnitExpr

-- | Single binding v<n>' = i
mkIntLitExprBinds :: Int -> GenType -> Integer -> ExprBinds
mkIntLitExprBinds n t i = mkSingleExprBinds $ mkValVarBinding n t $ mkIntLitExpr t i

-- | Single binding v<n>' = c
-- in C a character constant has type int!
mkCharLitExprBinds :: Int -> Char -> ExprBinds
mkCharLitExprBinds n i = mkSingleExprBinds $ mkValVarBinding n mkU32Type $ mkCharLitExpr i

-- | Single binding v<n>' = s
mkStringLitExprBinds :: Int -> String -> ExprBinds
mkStringLitExprBinds n s = mkSingleExprBinds $ mkValVarBinding n mkStringType $ mkStringLitExpr s

-- | Single binding v<n>' = b
mkBoolLitExprBinds :: Int -> Bool -> ExprBinds
mkBoolLitExprBinds n b = mkSingleExprBinds $ mkValVarBinding n mkBoolType $ mkBoolLitExpr b

-- | Single binding v<n>' = v
mkValVarExprBinds :: Int -> TypedVar -> ExprBinds
mkValVarExprBinds n v = mkSingleExprBinds $ mkValVarBinding n (typOfTV v) $ mkVarExpr v

-- | Member (field) access <v>{f=r<k>’} = e and v<n>’ = r<k>’
--   with putback <v> = <v>{f=r<k>’}
mkMemExprBinds :: Int -> Int -> CCS.FieldName -> ExprBinds -> ExprBinds
mkMemExprBinds n k f bp =
    mainbp
    where vv@(TV _ rt) = leadVar bp
          ct = getMemberType f rt
          cmp = TV (cmpVar k) ct
          rv = lvalVar bp
          rv' = if isErrVar rv then TV errVar rt else rv
          mainbp = addBinding (mkValVarBinding n ct $ mkVarExpr cmp) $
                     addBinding (mkBinding (mkRecTakePattern rv' cmp f) $ mkVarExpr vv) bp

-- | Array access (<v> @{@v<l>’=r<k>’},i<k>') = (v<n>',v<l>') and v<n>’ = r<k>’
--   with putback <v> = <v> @{@i<k>'=r<k>’}
mkIdxExprBinds :: Int -> Int -> ExprBinds -> ExprBinds -> ExprBinds
mkIdxExprBinds n k bp1 bp2 =
    mainbp -- if isErrVar rv then mainbp else addPutback (mkVarBinding rv $ mkArrPutExpr rv cmp idx) mainbp
    where v1@(TV _ at) = leadVar bp1
          v2@(TV _ it) = leadVar bp2
          et = getDerefType at
          cmp = TV (cmpVar k) et
          idx = TV (idxVar k) it
          rv = lvalVar bp1
          rv' = if isErrVar rv then TV errVar at else rv
          mainbp = addBinding (mkValVarBinding n et $ mkVarExpr cmp) $
                     addBinding (mkBinding (mkArrTakePattern rv' cmp idx v2) $ mkVarTupleExpr [v1,v2]) $ concatExprBinds [bp2,bp1]

-- | Pointer dereference, always <v>{cont=r<k>’} = v<n>' and v<n>’ = r<k>’
--   with putback <v> = <v>{cont=r<k>’}
-- The type of v<n>' may be an arbitrary mapped C pointer type except function pointer type.
mkDerefExprBinds :: Int -> Int -> ExprBinds -> ExprBinds
mkDerefExprBinds n k bp =
    mainbp -- if isErrVar rv then mainbp else addPutback (mkVarBinding rv $ mkRecPutExpr rv cmp f) mainbp
    where f = ptrDerivCompName
          vv@(TV _ rt) = leadVar bp
          ct = getDerefType rt
          cmp = TV (cmpVar k) ct
          rv = lvalVar bp
          rv' = if isErrVar rv then TV errVar rt else rv
          mainbp = addBinding (mkValVarBinding n ct $ mkVarExpr cmp) $
                     addBinding (mkBinding (mkRecTakePattern rv' cmp f) $ mkVarExpr vv) bp

-- | Operator application v<n>' = op [bp...]
mkOpExprBinds :: Int -> GenType -> CCS.OpName -> [ExprBinds] -> ExprBinds
mkOpExprBinds n t op bps =
    addBinding (mkValVarBinding n t $ mkOpExpr t op (map mkVarExpr vs)) $ concatExprBinds bps
    where vs = map leadVar bps 

-- | Application of constant named function v<n>' = f ()
mkConstAppExprBinds :: Int -> TypedFun -> ExprBinds
mkConstAppExprBinds n f = mkSingleExprBinds $ mkValVarBinding n (funResultType f) $ mkAppExpr (mkFunExpr f) mkUnitExpr

-- | Function pointer dereference f = fromFunPtr (fp)
-- The first argument is the type of the resulting function.
mkFunDerefExprBinds :: Int -> GenType -> ExprBinds -> ExprBinds
mkFunDerefExprBinds n ft bp =
    addBinding (mkValVarBinding n ft $ mkAppExpr (mkTopLevelFunExpr ("fromFunPtr",ffpt) [Just ft, Just fpt]) (mkVarExpr v)) bp
    where v@(TV _ fpt) = leadVar bp
          ffpt = mkFunType fpt ft

-- | Function application v = f (pbp) or (v,v1,..,vn) = f (pbp)
-- The first argument is the ExprBinds for the function
-- The second argument is the pattern for binding the function result
-- The third argument is the list of ExprBinds for the parameter tuple (or single parameter or unit value)
mkAppExprBinds :: ExprBinds -> GenIrrefPatn -> [ExprBinds] -> ExprBinds
mkAppExprBinds fbp rpat pbps =
    addBinding (mkBinding rpat $ mkAppExpr (mkVarExpr $ leadVar fbp) (mkTupleExpr (map (mkVarExpr . leadVar) pbps))) $ concatExprBinds (fbp : pbps)

-- | Assignment v<m>' = el op er, (v<n>',v) = (v<m>',v<m>') or (v,v<m>')
-- The first argument is True for a postfix inc/dec operator, otherwise false.
-- The second argument is a pair of the operator op for constructing the new value and its result type.
-- For plain assignment, op is "" and the type is the unit type.
-- The third argument is the operator argument expression or the assigned expression for a plain assignment.
-- The fourth argument is the lvalue ExprBinds.
mkAssExprBinds :: Int -> Int -> Bool -> (CCS.OpName, GenType) -> ExprBinds -> ExprBinds -> ExprBinds
mkAssExprBinds m n post (op,t) bpr bpl =
    addBinding lval $ addBinding (mkValVarBinding m (typOfGE er') er') bpl
    where vl = leadVar bpl
          vr = leadVar bpr
          el = mkVarExpr vl
          er = mkVarExpr vr
          er' = if null op then er else mkOpExpr t op [el,er]
          v = lvalVar bpl
          e = mkVarExpr v
          vres = TV (valVar n) (typOfGE er')
          eres = mkVarExpr $ TV (valVar m) (typOfGE er')
          lval = mkVarsTupleBinding [vres,v] [if post then e else eres, eres]

-- | Conditional v<n>' = if bp1 then bp2 else bp3
mkIfExprBinds :: Int -> ExprBinds -> ExprBinds -> ExprBinds -> ExprBinds
mkIfExprBinds n bp0 bp1 bp2 =
    addBinding (mkVarsBinding (vr : set) (mkIfExpr rts (mkVarExpr v0) e1 e2)) bp
    where set1 = sideEffectTargets bp1
          set2 = sideEffectTargets bp2
          v0 = leadVar bp0
          v1 = leadVar bp1
          v2 = leadVar bp2
          set = union set1 set2
          rt = adaptTypes (typOfTV v1) (typOfTV v2)
          rts = mkTupleType (rt : (map typOfTV set))
          vr = TV (valVar n) rt
          (bp1l,e1) = if null set1
                         then ([bp1],mkVarTupleExpr (v1 : set))
                         else ([],boundExpr $ cmbExtBinds set bp1)
          (bp2l,e2) = if null set2
                         then ([bp2],mkVarTupleExpr (v2 : set))
                         else ([],boundExpr $ cmbExtBinds set bp2)
          bp = concatExprBinds (bp0 : (bp1l ++ bp2l))

-- | Add binding to the main list
addBinding :: GenBnd -> ExprBinds -> ExprBinds
addBinding b (main,_) = (main ++ [b], (head $ boundVars b, lvalVarInExpr $ boundExpr b))

-- | Concatenate binding list pairs in order.
-- The first binding list pair is evaluated first
concatExprBinds :: [ExprBinds] -> ExprBinds
concatExprBinds [] = mkEmptyExprBinds
concatExprBinds bps = (concat mains, (val, lval))
    where mains = map fst bps
          val = fst $ snd $ head $ reverse bps
          lval = snd $ snd $ head $ reverse bps

-- | Append the putback list to the main list and use a new empty putback list.
-- Rebind a non-wildcard leadvar of the main list afterwards, if the putback list was not empty.
joinPutbacks :: ExprBinds -> [GenBnd] -> ExprBinds
joinPutbacks bp [] = bp
joinPutbacks bp@(main,_) putback = (main ++ putback, (tv, Nothing))
    where tv = leadVar bp

-- Construct Bindings
---------------------

-- construct p = expr
mkBinding :: GenIrrefPatn -> GenExpr -> GenBnd
mkBinding ip e = CS.Binding ip Nothing e []

-- | Single binding c' = gencotDummy msg
mkDummyBinding :: String -> GenBnd
mkDummyBinding msg = mkVarBinding typedCtlVar $ mkDummyExpr mkCtlType msg

-- construct () = ()
mkUnitBinding :: GenBnd
mkUnitBinding = mkBinding mkUnitPattern mkUnitExpr

-- construct (p1,..,pn) = expr or p1 = expr
mkTupleBinding :: [GenIrrefPatn] -> GenExpr -> GenBnd
mkTupleBinding ps e = mkBinding (mkTuplePattern ps) e

-- construct (v1,..,vn) = expr or v1 = expr
mkVarsBinding :: [TypedVar] -> GenExpr -> GenBnd
mkVarsBinding vs e = mkTupleBinding (map mkVarPattern vs) e

-- construct v = expr
mkVarBinding :: TypedVar -> GenExpr -> GenBnd
mkVarBinding v e = mkBinding (mkVarPattern v) e

-- construct v<n>' = expr
mkValVarBinding :: Int -> GenType -> GenExpr -> GenBnd
mkValVarBinding n t e = mkBinding (mkValVarPattern n t) e

-- construct (v1,..,vn) = (e1,..,en)
mkVarsTupleBinding :: [TypedVar] -> [GenExpr] -> GenBnd
mkVarsTupleBinding [v] [e] = mkVarBinding v e
mkVarsTupleBinding vs es = mkVarsBinding vs $ mkTupleExpr es

-- construct <v> = <v>{f=r<k>’}
mkRecPutBinding :: Int -> CCS.FieldName -> TypedVar -> GenBnd
mkRecPutBinding n f rv = if isErrVar rv then mkUnitBinding else mkVarBinding rv $ mkRecPutExpr rv cmp f
    where cmp = TV (cmpVar n) $ getMemberType f $ typOfTV rv

-- construct <v> = <v> @{@i<k>'=r<k>’}
mkArrPutBinding :: Int -> TypedVar -> TypedVar -> GenBnd
mkArrPutBinding n iv av = if isErrVar av then mkUnitBinding else mkVarBinding av $ mkArrPutExpr av cmp idx
    where cmp = TV (cmpVar n) $ getDerefType $ typOfTV av
          idx = TV (idxVar n) $ typOfTV iv

-- construct <v> = <v>{cont=r<k>’}
mkDerefPutBinding :: Int -> TypedVar -> GenBnd
mkDerefPutBinding n rv = if isErrVar rv then mkUnitBinding else mkVarBinding rv $ mkRecPutExpr rv cmp ptrDerivCompName
    where cmp = TV (cmpVar n) $ getDerefType $ typOfTV rv

-- replace p in (p,p1,...,pn) = expr or p = expr
replaceLeadPatn :: GenIrrefPatn -> GenBnd -> GenBnd
replaceLeadPatn ip (CS.Binding (GenIrrefPatn (CS.PTuple ps) _ _) _ e _) = mkTupleBinding (ip : tail ps) e
replaceLeadPatn ip' (CS.Binding ip _ e _) = mkBinding ip' e

-- | Null statement: c' = 0
mkNullBinding :: GenBnd
mkNullBinding = mkVarBinding typedCtlVar $ mkCtlLitExpr 0

-- | Expression statement: (c',v1..) = let ... in (0,v1..)
mkExpBinding :: ExprBinds -> GenBnd
mkExpBinding bp = mkVarsBinding (typedCtlVar : vs) $ mkLetExpr (binds bp) $ mkCtlVarTupleExpr 0 vs
    where vs = sideEffectTargets bp

-- | Return statement: (c',r',v1..) = let ... in (3, v<n>',v1,..)
-- First argument is the result type of the enclosing function.
mkRetBinding :: GenType -> ExprBinds -> GenBnd
mkRetBinding t bp = mkVarsBinding (typedCtlVar : ((TV resVar t) : vs)) $ mkLetExpr (binds bp) $ mkCtlVarTupleExpr 3 (v : vs)
    where v = leadVar bp
          vs = sideEffectTargets bp

-- | Break statement: c' = 2
mkBreakBinding :: GenBnd
mkBreakBinding = mkVarBinding typedCtlVar $ mkCtlLitExpr 2

-- | Continue statement: c' = 1
mkContBinding :: GenBnd
mkContBinding = mkVarBinding typedCtlVar $ mkCtlLitExpr 1

-- | Conditional statement (c',z1..) = let (v<n>',v1..) = expr in if v<n>' then let b1 in (c',z1..) else let b2 in (c',z1..)
mkIfBinding :: ExprBinds -> GenBnd -> GenBnd -> GenBnd
mkIfBinding bp b1 b2 =
    mkVarsBinding vs $ mkLetExpr (binds bp) $ mkIfExpr (typOfGE evs) (mkVarExpr (leadVar bp)) e1 e2
    where set0 = sideEffectTargets bp
          set1 = sideEffectFilter $ boundVars b1
          set2 = sideEffectFilter $ boundVars b2
          vs = typedCtlVar : (union set0 $ union set1 set2)
          evs = mkVarTupleExpr vs
          e1 = mkLetExpr [b1] evs
          e2 = mkLetExpr [b2] evs

-- | Switch statement (c',z1..) = let (s',v1..) = expr and (s1',...) = (s' == expr1,...) 
--         and (c',x1..) = exprb in (if c'=2 then 0 else c',z1..)
-- mbps are the case label expression binding list pairs with Nothing representing the default statement.
mkSwitchBinding :: ExprBinds -> [Maybe ExprBinds] -> GenBnd -> GenBnd
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
          c = mkIfExpr mkCtlType (mkBoolOpExpr "==" [mkVarExpr typedCtlVar,mkCtlLitExpr 2]) (mkCtlLitExpr 0) (mkVarExpr typedCtlVar)

-- | Switch group (c',x1..) = if cond then let b in (c',x1..) else (0,x1..)
mkCaseBinding :: GenBnd -> Int -> Int -> Bool -> GenBnd
mkCaseBinding b nr grps dfltSeen = 
    if dfltSeen && nr == grps
       then mkVarsBinding vs $ mkLetExpr [b] evs
       else mkVarsBinding vs $ mkIfExpr (typOfGE evs) (cond dfltSeen) (mkLetExpr [b] evs) $ mk0VarTupleExpr set
    where set = sideEffectFilter $ boundVars b
          vs = typedCtlVar : set
          evs = mkVarTupleExpr vs
          cond False = mkDisjExpr $ map (mkVarExpr . typedCasVar) $ take nr $ iterate (1+) 1
          cond True = mkBoolOpExpr "not" [mkDisjExpr $ map (mkVarExpr . typedCasVar) $ take (grps-nr) $ iterate (1+) (nr+1)]

-- | Statement in Sequence (c',z1..) = let b in if c' > 0 then (c',z1..) else let bs in (c',z1..)
mkSeqBinding :: GenBnd -> GenBnd -> GenBnd
mkSeqBinding b bs =
    mkVarsBinding vs $ mkLetExpr [b] $ 
      mkIfExpr (typOfGE e) (mkBoolOpExpr ">" [mkVarExpr typedCtlVar,mkCtlLitExpr 0]) e $ mkLetExpr [bs] $ e
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
mkDecBinding :: TypedVar -> ExprBinds -> GenBnd -> GenBnd
mkDecBinding v bp b = 
    mkVarsBinding vs $ mkLetExpr (binds bp ++ [mkVarsBinding vs' e]) $ mkVarTupleExpr vs
    where setv = sideEffectTargets bp
          sety = sideEffectFilter $ boundVars b
          setu = delete v sety
          setz = union setv setu
          vs = typedCtlVar : setz
          vs' = typedCtlVar : setu
          e = mkLetExpr [mkVarBinding v $ mkVarExpr $ leadVar bp, b] $ mkVarTupleExpr vs'

-- | Declaration as sequence of declarators
mkDeclBinding :: [(TypedVar,ExprBinds)] -> GenBnd -> GenBnd
mkDeclBinding [] b = b
mkDeclBinding ((v,bp) : ds) b = mkDecBinding v bp $ mkDeclBinding ds b

-- | for statement: 
mkForBinding :: ExprBinds -> (Either (Maybe ExprBinds) [(TypedVar,ExprBinds)]) -> ExprBinds -> ExprBinds -> GenBnd -> GenBnd
mkForBinding bpm ebp1 bp2 bp3 b = 
    case ebp1 of
         (Left Nothing) -> bindloop
         (Left (Just bp1)) -> mkSimpSeqBinding (cmbBinds bp1) bindloop
         (Right ds) -> mkDeclBinding ds bindloop
    where b3 = cmbBinds bp3
          accvars = union (sideEffectFilter $ boundVars b) (sideEffectFilter $ boundVars b3)
          exprstep = mkLetExpr [b] $ mkIfExpr (typOfGE accexpr) ctlcond accexpr $ mkLetExpr [b3] $ mk0VarTupleExpr accvars
          b2@(CS.Binding _ _ expr2 _) = cmbBinds bp2
          freevars = union (getFreeTypedVars exprstep) (getFreeTypedVars expr2)
          accpat = mkVarTuplePattern (typedCtlVar : accvars) -- (c',y1..)
          accexpr = mkVarTupleExpr (typedCtlVar : accvars) -- (c',y1..)
          ctlvar = mkVarExpr typedCtlVar
          ctlcond = mkBoolOpExpr ">" [ctlvar,mkCtlLitExpr 1] -- c' > 1
          accpatwild = mkVarTuplePattern ((TV "_" mkCtlType) : accvars) -- (_,y1..)
          obsvars = freevars \\ accvars
          obsvpat = mkVarTuplePattern obsvars
          repeatctl = mkIfExpr mkCtlType (mkBoolOpExpr "==" [ctlvar,mkCtlLitExpr 2]) (mkCtlLitExpr 0) ctlvar
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
cmbBinds :: ExprBinds -> GenBnd
cmbBinds ([],_) = mkUnitBinding
cmbBinds ([b],_) = b
cmbBinds bp = cmbExtBinds (sideEffectTargets bp) bp

-- | Combine all bindings in a binding list pair to a single binding with given side effect targets.
cmbExtBinds :: [TypedVar] -> ExprBinds -> GenBnd
cmbExtBinds vs bp@(main,_) =
    mkVarsBinding vs' $ mkLetExpr main $ mkVarTupleExpr vs'
    where lv = leadVar bp
          vs' = if elem lv vs then vs else lv : vs

-- Construct Patterns
---------------------

genIrrefPatn t p = GenIrrefPatn p noOrigin t

mkUnitPattern :: GenIrrefPatn
mkUnitPattern = genIrrefPatn unitType CS.PUnitel

mkVarPattern :: TypedVar -> GenIrrefPatn
mkVarPattern v = genIrrefPatn (typOfTV v) $ CS.PVar $ namOfTV v

mkValVarPattern :: Int -> GenType -> GenIrrefPatn
mkValVarPattern n t = mkVarPattern $ TV (valVar n) t

mkTuplePattern :: [GenIrrefPatn] -> GenIrrefPatn
mkTuplePattern [] = genIrrefPatn unitType $ CS.PUnitel
mkTuplePattern [ip] = ip
mkTuplePattern ips = genIrrefPatn (mkTupleType (map typOfGIP ips)) $ CS.PTuple ips

-- construct (v1,..,vn)
mkVarTuplePattern :: [TypedVar] -> GenIrrefPatn
mkVarTuplePattern vs = mkTuplePattern $ map mkVarPattern vs

-- construct #{f1 = p1, ..., fn = pn}
mkRecordPattern :: [(CCS.FieldName,GenIrrefPatn)] -> GenIrrefPatn
mkRecordPattern flds = genIrrefPatn (mkRecordType (map (\(f,ip) -> (f,typOfGIP ip)) flds)) $ CS.PUnboxedRecord $ map Just flds

-- construct v1{f=v2}
mkRecTakePattern :: TypedVar -> TypedVar -> CCS.FieldName -> GenIrrefPatn
mkRecTakePattern tv1@(TV v1 t1) tv2 f = genIrrefPatn t1 $ CS.PTake v1 [Just (f, mkVarPattern tv2)]

-- construct (v1 @{@v4=v2},v3)
mkArrTakePattern :: TypedVar -> TypedVar -> TypedVar -> TypedVar -> GenIrrefPatn
mkArrTakePattern tv1@(TV v1 t1) tv2 tv3 tv4 =
    mkTuplePattern [genIrrefPatn t1 $ CS.PArrayTake v1 [(mkVarExpr tv4,mkVarPattern tv2)], ip3]
    where ip3 = mkVarPattern tv3
          ie3 = mkVarExpr tv3

-- Construct Alternative
------------------------

mkAlt :: GenIrrefPatn -> GenExpr -> GenAlt
mkAlt p e = CS.Alt (GenPatn (CS.PIrrefutable p) noOrigin $ typOfGIP p) CCS.Regular e

