{-# LANGUAGE PackageImports #-}
module Gencot.Cogent.Ast where

import "language-c" Language.C

import Cogent.Surface as CS (TopLevel, Expr, Pattern, IrrefutablePattern, Type)
import Cogent.Common.Syntax (VarName)

import Gencot.Origin (Origin)
import Gencot.C.Ast as LQ (Stm)

data GenToplv = GenToplv { 
    toplOfGTL :: CS.TopLevel GenType GenIrrefPatn GenExpr,
    orgOfGTL :: Origin
    } deriving (Show)
data GenExpr = GenExpr {
    exprOfGE :: CS.Expr GenType GenPatn GenIrrefPatn () GenExpr,
    orgOfGE :: Origin,
    ccdOfGE :: Maybe LQ.Stm
    } deriving (Show)
data GenPatn = GenPatn { 
    patnOfGP :: CS.Pattern GenIrrefPatn,
    orgOfGP :: Origin
    } deriving (Show)
data GenIrrefPatn = GenIrrefPatn { 
    irpatnOfGIP :: CS.IrrefutablePattern VarName GenIrrefPatn GenExpr,
    orgOfGIP :: Origin
    } deriving (Show)
data GenType = GenType { 
    typeOfGT :: CS.Type GenExpr () GenType,
    orgOfGT :: Origin
    } deriving (Show)
