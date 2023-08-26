{-# LANGUAGE PackageImports, TypeSynonymInstances, FlexibleInstances #-}
module Gencot.Cogent.Post.Util where

import Data.List (nub,union,intersect,foldl1',(\\))
import Data.Functor.Identity (Identity)
import Data.Functor.Compose

import Language.C.Data.Error (CError)
import Language.C.Analysis.TravMonad (TravT,Trav)

import Cogent.Surface as CS
import Cogent.Common.Syntax as CCS

import Gencot.Traversal (runSubTrav)
import Gencot.Cogent.Ast
import Gencot.Cogent.Expr (mkUnitExpr, TypedVar(TV))

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
freeInExpr' (Var v) = [v]
freeInExpr' (Let bs bdy) = freeUnderBinding bs $ exprOfGE bdy
freeInExpr' (Match e _ alts) = union (freeInExpr e) (nub $ foldMap freeInAlt alts)
freeInExpr' (TLApp v ts _ _) = [v]
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

-- | Variables returned unmodified by an expression
-- In a binding a variable is not modified, if it is either not bound
-- or if it is bound but returned unmodified by the bound expression.
returnedByExpr :: GenExpr -> [VarName]
returnedByExpr e = returnedByExpr' $ exprOfGE e

returnedByExpr' :: ExprOfGE -> [VarName]
returnedByExpr' (Var v) = [v]
returnedByExpr' (Tuple es) = nub $ concat $ map returnedByExpr es
returnedByExpr' (If e0 _ e1 e2) =
    intersect (returnedByExpr e1) (returnedByExpr e2)
returnedByExpr' (Match _ _ alts) =
    foldl1' intersect $ map (\(Alt p _ e) -> returnedByExpr e) alts
returnedByExpr' (Let bs bdy) = returnedByLet bs bdy
returnedByExpr' _ = []

returnedByLet :: [GenBnd] -> GenExpr -> [VarName]
returnedByLet [] bdy = returnedByExpr bdy
returnedByLet (b : bs) bdy =
    (returnedByLet bs bdy) \\ (modifiedByBinding b)

modifiedByBinding :: GenBnd -> [VarName]
modifiedByBinding (Binding ip _ e _) = (freeInIrrefPatn ip) \\ (returnedByExpr e)

modifiedByBindings :: [GenBnd] -> [VarName]
modifiedByBindings [] = []
modifiedByBindings (b : bs) = union (modifiedByBinding b) (modifiedByBindings bs)

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
freeTypedVarsInExpr (GenExpr (TLApp v ts _ _) _ t _) = [TV v t]
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


{- Convert patterns and expressions to lists -}

getIPatternsList :: GenIrrefPatn -> [GenIrrefPatn]
getIPatternsList (GenIrrefPatn (PTuple ips) _ _) = ips
getIPatternsList ip = [ip]

getExprList :: GenExpr -> [GenExpr]
getExprList (GenExpr (Tuple es) _ _ _) = es
getExprList e = [e]


