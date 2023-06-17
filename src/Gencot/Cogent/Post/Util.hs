{-# LANGUAGE PackageImports, TypeSynonymInstances, FlexibleInstances #-}
module Gencot.Cogent.Post.Util where

import Data.List (nub,union,(\\))
import Data.Functor.Identity (Identity)
import Data.Functor.Compose

import Language.C.Data.Error (CError)
import Language.C.Analysis.TravMonad (TravT,Trav)

import Cogent.Surface as CS
import Cogent.Common.Syntax as CCS

import Gencot.Traversal (runSubTrav)
import Gencot.Cogent.Ast
import Gencot.Cogent.Expr (mkUnitExpr)

-- | Monad with empty user state, used only for error recording.
type ETrav = TravT () Identity

instance MonadFail ETrav where
  fail = error "ETrav monad failed"

-- | Run a sub traversal for a GenExpr, using the unit expression as default.
runExprTrav :: s -> Trav s GenExpr -> Trav s' (GenExpr,s,[CError])
runExprTrav ustate action = runSubTrav mkUnitExpr ustate action

isValVar :: CCS.VarName -> Bool
isValVar "" = False
isValVar v = (head v == 'v') && (last v == '\'')

isCVar :: CCS.VarName -> Bool
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

-- | Free variables in a sequence of bindings.
freeInBindings :: [GenBnd] -> [VarName]
freeInBindings bs = freeUnderBinding bs CS.Unitel

-- | Variables bound in a sequence of bindings.
boundInBindings :: [GenBnd] -> [VarName]
boundInBindings [] = []
boundInBindings ((Binding ipb Nothing eb _) : bs) = union (freeInIrrefPatn ipb) $ boundInBindings bs

{- Convert patterns and expressions to lists -}

getIPatternsList :: GenIrrefPatn -> [GenIrrefPatn]
getIPatternsList (GenIrrefPatn (PTuple ips) _ _) = ips
getIPatternsList ip = [ip]

getExprList :: GenExpr -> [GenExpr]
getExprList (GenExpr (Tuple es) _ _ _) = es
getExprList e = [e]


