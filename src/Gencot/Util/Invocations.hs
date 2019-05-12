{-# LANGUAGE PackageImports, TypeSynonymInstances, FlexibleInstances #-}
module Gencot.Util.Invocations where

import Data.Set (Set,empty,union,insert)
import Data.Foldable (foldlM)
import Control.Monad (liftM, liftM2)

import "language-c" Language.C as LC
import Language.C.Data.Ident as LCI
import Language.C.Data.Node as LCN
import Language.C.Data.Position as LCP
import Language.C.Syntax.AST as LCS
import qualified Language.C.Analysis as LCA

import Gencot.Traversal (FTrav)

unionM = liftM2 union

class HasInvs a where
  getInvocations :: a -> FTrav (Set Ident)
  mgetInvocations :: (Maybe a) -> FTrav (Set Ident)
  mgetInvocations = maybe (return empty) getInvocations
  
instance HasInvs a => HasInvs [a] where
    getInvocations = foldlM accunion empty
        where accunion s el = (liftM (union s)) (getInvocations el)

instance HasInvs LCA.DeclEvent where
    getInvocations (LCA.DeclEvent (LCA.FunctionDef (LCA.FunDef _ stat _))) = getInvocations stat
    getInvocations _ = return empty

instance HasInvs LC.CBlockItem where
    getInvocations (LC.CBlockStmt stat) = getInvocations stat
    getInvocations _ = return empty
    
instance HasInvs LCA.Stmt where
    getInvocations (LC.CExpr mexpr _) = mgetInvocations mexpr
    getInvocations (LC.CLabel _ stat _ _) = getInvocations stat
    getInvocations (LC.CCase expr stat _) = unionM (getInvocations expr) (getInvocations stat)
    getInvocations (LC.CDefault stat _) = getInvocations stat
    getInvocations (LC.CCompound _ bis _) = getInvocations bis
    getInvocations (LC.CIf expr stat mestat _) = 
        unionM (getInvocations expr) 
        $ unionM (getInvocations stat) (mgetInvocations mestat)
    getInvocations (LC.CSwitch expr stat _) = unionM (getInvocations expr) (getInvocations stat)
    getInvocations (LC.CWhile expr stat _ _) = unionM (getInvocations expr) (getInvocations stat)
    getInvocations (LC.CFor exdec mcond mstep stat _) = 
        unionM ((either mgetInvocations (\_ -> (return empty))) exdec) 
        $ unionM (mgetInvocations mcond)
        $ unionM (mgetInvocations mstep) (getInvocations stat)
    getInvocations (LC.CReturn mexpr _) = mgetInvocations mexpr
    getInvocations _ = return empty
    
instance HasInvs LC.CExpr where
    getInvocations (LC.CCall (LC.CVar ident _) args _) = (liftM (insert ident)) (getInvocations args)
    getInvocations (LC.CCall expr args _) = unionM (getInvocations expr) (getInvocations args)
    getInvocations (LC.CComma exprs _) = getInvocations exprs
    getInvocations (LC.CAssign _ expr1 expr2 _) = unionM (getInvocations expr1) (getInvocations expr2)
    getInvocations (LC.CCond expr1 mexpr2 expr3 _) = 
        unionM (getInvocations expr1) $ unionM (mgetInvocations mexpr2) (getInvocations expr3)
    getInvocations (LC.CBinary _ expr1 expr2 _) = unionM (getInvocations expr1) (getInvocations expr2)
    getInvocations (LC.CCast _ expr _) = getInvocations expr
    getInvocations (LC.CUnary _ expr _) = getInvocations expr
    getInvocations (LC.CIndex expr1 expr2 _) = unionM (getInvocations expr1) (getInvocations expr2)
    getInvocations (LC.CMember expr _ _ n) = getInvocations expr
    getInvocations _ = return empty
