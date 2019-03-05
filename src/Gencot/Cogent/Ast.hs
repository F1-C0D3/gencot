{-# LANGUAGE PackageImports #-}
module Gencot.Cogent.Ast where

import "language-c" Language.C

--import "language-c-quote" Language.C.Syntax as LQ (Exp,Stm)

import Cogent.Surface as CS (TopLevel, IrrefutablePattern, Type)
import Cogent.Common.Syntax (VarName)

import Gencot.Origin (Origin)
import Gencot.C.Ast as LQ (Exp,Stm)

data GenExpr = ConstExpr LQ.Exp
             | FunBody LQ.Stm deriving (Show)

data GenToplv = GenToplv { 
    toplOfGTL :: CS.TopLevel GenType GenIrrefPatn GenExpr,
    orgOfTL :: Origin
    }  deriving (Show)
data GenIrrefPatn = GenIrrefPatn { 
    irpatnOfGIP :: CS.IrrefutablePattern VarName GenIrrefPatn,
    orgOfIP :: Origin
    } deriving (Show)
data GenType = GenType { 
    typeOfGT :: CS.Type GenExpr GenType,
    orgOfT :: Origin
    } deriving (Show)
{-
type OStat = CStatement Origin
type OExpr = CExpression Origin
type OConst = CConstant Origin

class ONode a where
  nodeOrigin :: a -> Origin
instance ONode Origin where
  nodeOrigin = id
instance (ONode a, ONode b) => ONode (Either a b) where
  nodeOrigin = either nodeOrigin nodeOrigin

instance ONode t1 => ONode (CExpression t1) where
        nodeOrigin (CComma _ n) = nodeOrigin n
        nodeOrigin (CAssign _ _ _ n) = nodeOrigin n
        nodeOrigin (CCond _ _ _ n) = nodeOrigin n
        nodeOrigin (CBinary _ _ _ n) = nodeOrigin n
        nodeOrigin (CCast _ _ n) = nodeOrigin n
        nodeOrigin (CUnary _ _ n) = nodeOrigin n
        nodeOrigin (CSizeofExpr _ n) = nodeOrigin n
        nodeOrigin (CSizeofType _ n) = nodeOrigin n
        nodeOrigin (CAlignofExpr _ n) = nodeOrigin n
        nodeOrigin (CAlignofType _ n) = nodeOrigin n
        nodeOrigin (CComplexReal _ n) = nodeOrigin n
        nodeOrigin (CComplexImag _ n) = nodeOrigin n
        nodeOrigin (CIndex _ _ n) = nodeOrigin n
        nodeOrigin (CCall _ _ n) = nodeOrigin n
        nodeOrigin (CMember _ _ _ n) = nodeOrigin n
        nodeOrigin (CVar _ n) = nodeOrigin n
        nodeOrigin (CConst d) = nodeOrigin d
        nodeOrigin (CCompoundLit _ _ n) = nodeOrigin n
        nodeOrigin (CGenericSelection _ _ n) = nodeOrigin n
        nodeOrigin (CStatExpr _ n) = nodeOrigin n
        nodeOrigin (CLabAddrExpr _ n) = nodeOrigin n
     --   nodeOrigin (CBuiltinExpr d) = nodeOrigin d

instance ONode t1 => ONode (CConstant t1) where
        nodeOrigin (CIntConst _ n) = nodeOrigin n
        nodeOrigin (CCharConst _ n) = nodeOrigin n
        nodeOrigin (CFloatConst _ n) = nodeOrigin n
        nodeOrigin (CStrConst _ n) = nodeOrigin n

instance ONode t1 => ONode (CStatement t1) where
        nodeOrigin (CLabel _ _ _ n) = nodeOrigin n
        nodeOrigin (CCase _ _ n) = nodeOrigin n
        nodeOrigin (CCases _ _ _ n) = nodeOrigin n
        nodeOrigin (CDefault _ n) = nodeOrigin n
        nodeOrigin (CExpr _ n) = nodeOrigin n
        nodeOrigin (CCompound _ _ n) = nodeOrigin n
        nodeOrigin (CIf _ _ _ n) = nodeOrigin n
        nodeOrigin (CSwitch _ _ n) = nodeOrigin n
        nodeOrigin (CWhile _ _ _ n) = nodeOrigin n
        nodeOrigin (CFor _ _ _ _ n) = nodeOrigin n
        nodeOrigin (CGoto _ n) = nodeOrigin n
        nodeOrigin (CGotoPtr _ n) = nodeOrigin n
      --  nodeOrigin (CCont d) = nodeOrigin d
      --  nodeOrigin (CBreak d) = nodeOrigin d
        nodeOrigin (CReturn _ n) = nodeOrigin n
        nodeOrigin (CAsm _ n) = nodeOrigin n
-}
