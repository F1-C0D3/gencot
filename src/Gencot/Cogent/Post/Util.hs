{-# LANGUAGE PackageImports, TypeSynonymInstances, FlexibleInstances #-}
module Gencot.Cogent.Post.Util where

import Data.List (nub,union,(\\))
import Data.Functor.Identity (Identity)

import Language.C.Analysis.TravMonad (TravT,Trav)

import Cogent.Surface as CS
import Cogent.Common.Syntax as CCS

import Gencot.Traversal (runTravWithErrors)
import Gencot.Cogent.Ast
import Gencot.Cogent.Expr (mkUnitExpr)

-- | Monad with empty user state, used only for error recording.
type ETrav = TravT () Identity

instance MonadFail ETrav where
  fail = error "ETrav monad failed"

runTravExpr :: s -> Trav s GenExpr -> Trav s' (GenExpr,s)
runTravExpr ustate action = runTravWithErrors (mkUnitExpr,ustate) action

isValVar :: CCS.VarName -> Bool
isValVar "" = False
isValVar v = (head v == 'v') && (last v == '\'')

isLiteralExpr :: ExprOfGE -> Bool
isLiteralExpr (IntLit _) = True
isLiteralExpr (BoolLit _) = True
isLiteralExpr (CharLit _) = True
isLiteralExpr (StringLit _) = True
isLiteralExpr _ = False

-- | Free variables in a pattern.
freeInPatn :: GenPatn -> [VarName]
freeInPatn = nub . CS.fvP . toRawPatn

-- | Free variables in an irrefutable pattern.
freeInIrrefPatn :: GenIrrefPatn -> [VarName]
freeInIrrefPatn = nub . CS.fvIP . toRawIrrefPatn

-- | Free variables in an expression.
freeInExpr' :: ExprOfGE -> [VarName]
freeInExpr' = nub . CS.fvE . toRawExpr'

-- | Free variables in an expression.
freeInExpr :: GenExpr -> [VarName]
freeInExpr = nub . CS.fvE . toRawExpr

-- | Free variables in a let expression, given by a sequence of bindings and the body.
freeUnderBinding :: [GenBnd] -> ExprOfGE -> [VarName]
freeUnderBinding [] e = freeInExpr' e
freeUnderBinding ((CS.Binding ipb Nothing eb []) : bs) e =
    nub ((freeInExpr eb) ++ ((freeUnderBinding bs e) \\ (freeInIrrefPatn ipb)))
freeUnderBinding (b : _) _ = error ("unexpected binding in freeUnderBinding: " ++ (show b))

-- | Free variables in a sequence of bindings.
freeInBindings :: [GenBnd] -> [VarName]
freeInBindings bs = freeUnderBinding bs CS.Unitel

-- | Variables bound in a sequence of bindings.
boundInBindings :: [GenBnd] -> [VarName]
boundInBindings [] = []
boundInBindings ((CS.Binding ipb Nothing eb []) : bs) = union (freeInIrrefPatn ipb) $ boundInBindings bs
boundInBindings (b : _) = error ("unexpected binding in boundInBindings: " ++ (show b))


