{-# LANGUAGE PackageImports #-}
module Gencot.Cogent.Ast where

import "language-c" Language.C

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
