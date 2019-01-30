{-# LANGUAGE PackageImports #-}
module Gencot.Cogent.Ast where

import "language-c" Language.C (CExpr,CStat)

import Cogent.Surface (TopLevel, IrrefutablePattern, Type)
import Cogent.Common.Syntax (VarName)

import Gencot.Origin (Origin)

data GenExpr = ConstExpr CExpr
             | FunBody CStat deriving (Show)

data GenToplv = GenToplv { 
    orgOfTL :: Origin, 
    toplOfGTL :: TopLevel GenType GenIrrefPatn GenExpr 
    }  deriving (Show)
data GenIrrefPatn = GenIrrefPatn { 
    orgOfIP :: Origin, 
    irpatnOfGIP :: IrrefutablePattern VarName GenIrrefPatn 
    } deriving (Show)
data GenType = GenType { 
    orgOfT :: Origin, 
    typeOfGT :: Type GenExpr GenType 
    } deriving (Show)


