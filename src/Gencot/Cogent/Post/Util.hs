{-# LANGUAGE PackageImports, TypeSynonymInstances, FlexibleInstances #-}
module Gencot.Cogent.Post.Util where

import Data.List (replicate,transpose,nub,union,intersect,(\\))
import Data.Maybe (catMaybes)
import Data.Functor.Identity (Identity)
import Data.Functor.Compose

import Language.C.Data.Error (CError)
import Language.C.Analysis.TravMonad (TravT,Trav)

import Cogent.Surface as CS
import Cogent.Common.Syntax as CCS

import Gencot.Traversal (runSubTrav)
import Gencot.Cogent.Ast
import Gencot.Cogent.Expr (mkUnitExpr, TypedVar(TV))
import Gencot.Cogent.Types (getResultType, tupleSize)

-- | Monad with empty user state, used only for error recording.
type ETrav = TravT () Identity

instance MonadFail ETrav where
  fail = error "ETrav monad failed"

-- | Run a sub traversal for a GenExpr, using the unit expression as default.
runExprTrav :: s -> Trav s GenExpr -> Trav s' (GenExpr,s,[CError])
runExprTrav ustate action = runSubTrav mkUnitExpr ustate action

isValVar :: VarName -> Bool
isValVar "" = False
isValVar v = (head v == 'v') && (last v == '\'')

isCVar :: VarName -> Bool
isCVar "" = False
isCVar v = last v /= '\''

isLiteralExpr :: ExprOfGE -> Bool
isLiteralExpr (IntLit _) = True
isLiteralExpr (BoolLit _) = True
isLiteralExpr (CharLit _) = True
isLiteralExpr (StringLit _) = True
isLiteralExpr _ = False

-- | Free variables in an alternative.
freeInAlt :: GenAlt -> [VarName]
freeInAlt (Alt p _ e) =
    let locals = freeInPatn p
    in filter (`notElem` locals) (freeInExpr e)

-- | Free variables (bound) in a pattern.
freeInPatn :: GenPatn -> [VarName]
{- freeInPatn = nub . CS.fvP . toRawPatn -}
freeInPatn (GenPatn (PIrrefutable ip) _ _) = freeInIrrefPatn ip
freeInPatn _ = []

-- | Free variables (bound) in an irrefutable pattern.
freeInIrrefPatn :: GenIrrefPatn -> [VarName]
{- freeInIrrefPatn = nub . CS.fvIP . toRawIrrefPatn -}
freeInIrrefPatn = freeInIrrefPatn' . irpatnOfGIP

freeInIrrefPatn' :: IrpatnOfGIP -> [VarName]
freeInIrrefPatn' (PVar pv) = [pv]
freeInIrrefPatn' (PTuple ips) = nub $ foldMap freeInIrrefPatn ips
freeInIrrefPatn' (PUnboxedRecord mfs) = nub $ foldMap (freeInIrrefPatn . snd) (Compose mfs)
freeInIrrefPatn' (PTake pv mfs) = nub (pv : foldMap (freeInIrrefPatn . snd) (Compose mfs))
freeInIrrefPatn' (PArrayTake pv hs) = nub (pv : foldMap (freeInIrrefPatn . snd) hs)
freeInIrrefPatn' _ = []

-- | Free variables occurring in (an index) in an irrefutable pattern.
freeInIndex :: GenIrrefPatn -> [VarName]
freeInIndex (GenIrrefPatn (PTuple ips) _ _) = nub $ foldMap freeInIndex ips
freeInIndex (GenIrrefPatn (PArrayTake _ hs) _ _) = nub $ foldMap (freeInExpr . fst) hs
freeInIndex _ = []

-- | Free variables in an expression.
freeInExpr :: GenExpr -> [VarName]
{- freeInExpr = nub . CS.fvE . toRawExpr -}
freeInExpr = freeInExpr' . exprOfGE

freeInExpr' :: ExprOfGE -> [VarName]
{- freeInExpr' = nub . CS.fvE . toRawExpr' -}
freeInExpr' (Var v) | v == "gencotDummy" = []
freeInExpr' (Var v) = [v]
freeInExpr' (Let bs bdy) = freeUnderBinding bs $ exprOfGE bdy
freeInExpr' (Match e _ alts) = union (freeInExpr e) (nub $ foldMap freeInAlt alts)
freeInExpr' (TLApp v ts _ _) = [] -- toplevel functions are not returned as free variables
freeInExpr' (Lam p t e) = filter (`notElem` freeInIrrefPatn p) (freeInExpr e)
freeInExpr' e = nub $ foldMap freeInExpr e

-- | Free variables in a let expression, given by a sequence of bindings and the body.
-- Banged variables are not considered to be free because their type is changed,
-- therefore they cannot be substituted from the context.
freeUnderBinding :: [GenBnd] -> ExprOfGE -> [VarName]
freeUnderBinding [] e = freeInExpr' e
freeUnderBinding ((Binding ipb Nothing eb bvs) : bs) e =
    nub (((freeInExpr eb) \\ bvs) ++ (freeInIndex ipb) ++((freeUnderBinding bs e) \\ (freeInIrrefPatn ipb)))

freeInBinding :: GenBnd -> [VarName]
freeInBinding (Binding ipb Nothing eb bvs) =
    union ((freeInExpr eb) \\ bvs) (freeInIndex ipb)

-- | Free variables in a sequence of bindings.
freeInBindings :: [GenBnd] -> [VarName]
freeInBindings bs = freeUnderBinding bs CS.Unitel

-- | Variables bound in a sequence of bindings.
boundInBindings :: [GenBnd] -> [VarName]
boundInBindings [] = []
boundInBindings ((Binding ipb Nothing eb _) : bs) = union (freeInIrrefPatn ipb) $ boundInBindings bs

{- Variables (not) modified by a re-binding -}

-- | Variables returned unmodified by the components of an expression.
-- For other components the result is the empty string.
-- In a put expression the container is always considered modified.
returnedByExpr :: GenExpr -> [VarName]
returnedByExpr e = returnedByExpr' $ exprOfGE e

returnedByExpr' :: ExprOfGE -> [VarName]
returnedByExpr' (Var v) = [v]
returnedByExpr' (Tuple es) = concat $ map returnedByExpr es
returnedByExpr' (If e0 _ e1 e2) =
    map (\(v1,v2) -> if v1 == v2 then v1 else "") $ zip (returnedByExpr e1) (returnedByExpr e2)
returnedByExpr' (Match _ _ alts) =
    map (\vs -> if all (== (head vs)) vs then head vs else "") $ transpose $ map returnedByAlt alts
returnedByExpr' (Let bs bdy) = returnedByLet bs bdy
returnedByExpr' (App f e _) = replicate (tupleSize $ getResultType $ typOfGE f) ""
returnedByExpr' _ = [""]

returnedByAlt :: GenAlt -> [VarName]
returnedByAlt (CS.Alt p _ e) =
    map (\v -> if elem v $ freeInPatn p then "" else v) $ returnedByExpr e

returnedByLet :: [GenBnd] -> GenExpr -> [VarName]
returnedByLet [] bdy = returnedByExpr bdy
returnedByLet (b : bs) bdy =
    map (\v -> if elem v (modifiedByBinding b) then "" else v) (returnedByLet bs bdy)

boundTupleInIrrefPatn :: GenIrrefPatn -> [[VarName]]
boundTupleInIrrefPatn = boundTupleInIrrefPatn' . irpatnOfGIP

boundTupleInIrrefPatn' :: IrpatnOfGIP -> [[VarName]]
boundTupleInIrrefPatn' (PVar pv) = [[pv]]
boundTupleInIrrefPatn' (PTuple ips) = concat $ map boundTupleInIrrefPatn ips
boundTupleInIrrefPatn' (PUnboxedRecord mfs) = [nub $ foldMap (freeInIrrefPatn . snd) (Compose mfs)]
boundTupleInIrrefPatn' (PTake pv mfs) = [nub (pv : foldMap (freeInIrrefPatn . snd) (Compose mfs))]
boundTupleInIrrefPatn' (PArrayTake pv hs) = [nub (pv : foldMap (freeInIrrefPatn . snd) hs)]
boundTupleInIrrefPatn' _ = [[]]

-- | Variables modified by the components in a binding
-- In a binding component a variable is not modified, if it is either not bound
-- or if it is bound but returned unmodified by the bound expression.
-- In a take binding (only) the container is considered unmodified.
modifiedByBinding :: GenBnd -> [VarName]
modifiedByBinding (Binding ip _ e _) =
    nub $ concat $ map (\(vs,v) -> vs \\ [v]) $ zip (boundTupleInIrrefPatn ip) (returnedByExpr e)

modifiedByBindings :: [GenBnd] -> [VarName]
modifiedByBindings [] = []
modifiedByBindings (b : bs) = union (modifiedByBinding b) (modifiedByBindings bs)

{- Using Variables -}

-- | Test whether the value of a variable is used in an expression after a sequence of bindings.
-- The value is considered to be used if it occurs free in the expression under the bindings
-- or if it occurs free in a bound expression and the bound variable is used afterwards.
varUsedIn :: CCS.VarName -> [GenBnd] -> GenExpr -> Bool
varUsedIn v bs bdy = or $ varContribInLet v bs bdy

-- | The components of an expression to which a variable contributes.
-- The length of the result is the length of the tuple type of the expression.
varContrib :: CCS.VarName -> GenExpr -> [Bool]
varContrib v (GenExpr (CS.Tuple es) _ _ _) =
    concat $ map (varContrib v) es
varContrib v (GenExpr (CS.If e0 _ e1 e2) _ t _) | varContrib v e0 == [True] =
    replicate (tupleSize t) True
varContrib v (GenExpr (CS.If e0 _ e1 e2) _ _ _) =
    map (\(b1,b2) -> b1 || b2) $ zip (varContrib v e1) (varContrib v e2)
varContrib v (GenExpr (CS.Match e0 _ alts) _ t _) | varContrib v e0 == [True] =
    replicate (tupleSize t) True
varContrib v (GenExpr (CS.Match e0 _ alts) _ _ _) =
    map or $ transpose $ map (varContribInAlt v) alts
varContrib v (GenExpr (CS.Let bs bdy) _ _ _) =
    varContribInLet v bs bdy
varContrib v (GenExpr (CS.App f e _) _ _ _) =
    replicate ts $ ((or $ varContrib v e) || (varContrib v f == [True]))
    where ts = tupleSize $ getResultType $ typOfGE f
varContrib v e = [elem v $ freeInExpr e]

varContribInAlt :: CCS.VarName -> GenAlt -> [Bool]
varContribInAlt v (CS.Alt p _ e) | elem v $ freeInPatn p =
    replicate (tupleSize $ typOfGE e) False
varContribInAlt v (CS.Alt _ _ e) = varContrib v e

varContribInLet :: CCS.VarName -> [GenBnd] -> GenExpr -> [Bool]
varContribInLet v [] bdy = varContrib v bdy
varContribInLet v ((CS.Binding ip _ e _) : bs) bdy =
    map or $ transpose $ map (\v -> varContribInLet v bs bdy) vs'
    where vs = selectVars ip $ varContrib v e
          vs' = if elem v $ freeInIrrefPatn ip
                   then vs
                   else v : vs

selectVars :: GenIrrefPatn -> [Bool] -> [CCS.VarName]
selectVars (GenIrrefPatn (CS.PTuple ips) _ _) bs =
    concat $ map (\(ip,b) -> selectVars ip [b]) $ zip ips bs
selectVars (GenIrrefPatn (CS.PVar v) _ _) [b] = if b then [v] else []
selectVars (GenIrrefPatn (CS.PTake v [Just (_,GenIrrefPatn (CS.PVar cv) _ _)]) _ _) [b] =
    if b then [v,cv] else []
selectVars (GenIrrefPatn (CS.PArrayTake v [(_,GenIrrefPatn (CS.PVar cv) _ _)]) _ _) [b] =
    if b then [v,cv] else []
selectVars (GenIrrefPatn (CS.PUnboxedRecord mfs) _ _) [b] =
    concat $ map (\(_,ip) -> selectVars ip [b]) $ catMaybes mfs
selectVars _ _ = []


{- Exchanging Bindings -}

-- Two bindings are exchangeable if modified variables are disjoint (write-write conflict)
-- and variables modified by one do not occur free in the other (read-write conflict).

exchangeableWithBinding :: GenBnd -> GenBnd -> Bool
exchangeableWithBinding b1 b2 =
    (null $ intersect m1 m2) &&
    (null $ intersect m1 $ freeInBinding b2) &&
    (null $ intersect m2 $ freeInBinding b1)
    where m1 = modifiedByBinding b1
          m2 = modifiedByBinding b2

exchangeableWithBindings :: GenBnd -> [GenBnd] -> Bool
exchangeableWithBindings b bs =
    (null $ intersect m ms) &&
    (null $ intersect m $ freeInBindings bs) &&
    (null $ intersect ms $ freeInBinding b)
    where m = modifiedByBinding b
          ms = modifiedByBindings bs

{- Typed Variables -}

-- | Free typed variables in an expression.
-- These are the variables which must be bound in the context.
freeTypedVarsInExpr :: GenExpr -> [TypedVar]
freeTypedVarsInExpr (GenExpr (Var v) _ t _) = [TV v t]
freeTypedVarsInExpr (GenExpr (Tuple es) _ _ _) =
    nub $ concat $ map freeTypedVarsInExpr es
freeTypedVarsInExpr (GenExpr (Let bs bdy) _ _ _) =
    freeTypedVarsUnderBinding bs $ freeTypedVarsInExpr bdy
freeTypedVarsInExpr (GenExpr (Match e _ alts) _ _ _) = union (freeTypedVarsInExpr e) (nub $ foldMap freeTypedVarsInAlt alts)
freeTypedVarsInExpr (GenExpr (TLApp _ _ _ _) _ _ _) = [] -- toplevel functions are not returned as free variables
freeTypedVarsInExpr (GenExpr (Lam ip t e) _ _ _) = filter (`notElem` freeTypedVarsInIrrefPatn ip) (freeTypedVarsInExpr e)
freeTypedVarsInExpr e = nub $ foldMap freeTypedVarsInExpr $ exprOfGE e


freeTypedVarsInAlt :: GenAlt -> [TypedVar]
freeTypedVarsInAlt (Alt p _ e) =
    let locals = freeTypedVarsInPatn p
    in filter (`notElem` locals) (freeTypedVarsInExpr e)

-- | Free variables (bound) in a pattern.
freeTypedVarsInPatn :: GenPatn -> [TypedVar]
freeTypedVarsInPatn (GenPatn (PIrrefutable ip) _ _) = freeTypedVarsInIrrefPatn ip
freeTypedVarsInPatn _ = []

-- | Free variables (bound) in an irrefutable pattern.
freeTypedVarsInIrrefPatn :: GenIrrefPatn -> [TypedVar]
freeTypedVarsInIrrefPatn (GenIrrefPatn (PVar pv) _ t) = [TV pv t]
freeTypedVarsInIrrefPatn (GenIrrefPatn (PTuple ips) _ _) = nub $ foldMap freeTypedVarsInIrrefPatn ips
freeTypedVarsInIrrefPatn (GenIrrefPatn (PUnboxedRecord mfs) _ _) = nub $ foldMap (freeTypedVarsInIrrefPatn . snd) (Compose mfs)
freeTypedVarsInIrrefPatn (GenIrrefPatn (PTake pv mfs) _ t) = nub ((TV pv t) : foldMap (freeTypedVarsInIrrefPatn . snd) (Compose mfs))
freeTypedVarsInIrrefPatn (GenIrrefPatn (PArrayTake pv hs) _ t) = nub ((TV pv t) : foldMap (freeTypedVarsInIrrefPatn . snd) hs)
freeTypedVarsInIrrefPatn _ = []

-- | Free typed variables occurring in (an index) in an irrefutable pattern.
freeTypedVarsInIndex :: GenIrrefPatn -> [TypedVar]
freeTypedVarsInIndex (GenIrrefPatn (PTuple ips) _ _) = nub $ foldMap freeTypedVarsInIndex ips
freeTypedVarsInIndex (GenIrrefPatn (PArrayTake _ hs) _ _) = nub $ foldMap (freeTypedVarsInExpr . fst) hs
freeTypedVarsInIndex _ = []

-- | Free typed variables in a let expression, given by a sequence of bindings and the free typed variables in the body.
-- Banged variables are ignored because they must be bound in the context if they are free in the banged context.
freeTypedVarsUnderBinding :: [GenBnd] -> [TypedVar] -> [TypedVar]
freeTypedVarsUnderBinding [] fvs = fvs
freeTypedVarsUnderBinding ((Binding ip _ e bvs) : bs) fvs =
    nub ((freeTypedVarsInExpr e) ++ (freeTypedVarsInIndex ip) ++((freeTypedVarsUnderBinding bs fvs) \\ (freeTypedVarsInIrrefPatn ip)))

-- | Variables bound in a sequence of bindings.
boundTypedVarsInBindings :: [GenBnd] -> [TypedVar]
boundTypedVarsInBindings [] = []
boundTypedVarsInBindings ((Binding ipb Nothing eb _) : bs) = union (freeTypedVarsInIrrefPatn ipb) $ boundTypedVarsInBindings bs

{- Convert patterns and expressions to lists -}

getIPatternsList :: GenIrrefPatn -> [GenIrrefPatn]
getIPatternsList (GenIrrefPatn (PTuple ips) _ _) = ips
getIPatternsList ip = [ip]

getExprList :: GenExpr -> [GenExpr]
getExprList (GenExpr (Tuple es) _ _ _) = es
getExprList e = [e]


