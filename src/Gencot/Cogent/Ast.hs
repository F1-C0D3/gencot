{-# LANGUAGE PackageImports #-}
module Gencot.Cogent.Ast where

import "language-c" Language.C

import Cogent.Surface as CS (TopLevel, Expr, Pattern, IrrefutablePattern, Type, Binding, RawType(RT), RawPatn(RP), RawIrrefPatn(RIP), RawExpr(RE))
import Cogent.Dargent.Surface (DataLayoutExpr(DL), DataLayoutExpr'(LVar))
import Cogent.Common.Syntax (VarName)
import Cogent.Util (ffmap,fffmap,ffffmap,fffffmap)

import Gencot.Origin (Origin)
import Gencot.C.Ast as LQ (Stm)

type ToplOfGTL = CS.TopLevel GenType GenIrrefPatn GenExpr
type ExprOfGE = CS.Expr GenType GenPatn GenIrrefPatn () GenExpr
type PatnOfGP = CS.Pattern GenIrrefPatn
type IrpatnOfGIP = CS.IrrefutablePattern VarName GenIrrefPatn GenExpr
type TypeOfGT = CS.Type GenExpr () GenType

data GenToplv = GenToplv { 
    toplOfGTL :: ToplOfGTL,
    orgOfGTL :: Origin
    } deriving (Eq, Show)
data GenExpr = GenExpr {
    exprOfGE :: ExprOfGE,
    orgOfGE :: Origin,
    ccdOfGE :: Maybe LQ.Stm
    } deriving (Eq, Ord, Show)
data GenPatn = GenPatn { 
    patnOfGP :: PatnOfGP,
    orgOfGP :: Origin
    } deriving (Eq, Ord, Show)
data GenIrrefPatn = GenIrrefPatn { 
    irpatnOfGIP :: IrpatnOfGIP,
    orgOfGIP :: Origin
    } deriving (Eq, Ord, Show)
data GenType = GenType { 
    typeOfGT :: TypeOfGT,
    orgOfGT :: Origin
    } deriving (Eq, Ord, Show)

type GenBnd = CS.Binding GenType GenPatn GenIrrefPatn GenExpr

toRawType :: GenType -> RawType
toRawType = RT . fmap toRawType . ffmap toDLExpr . fffmap toRawExpr . typeOfGT

toRawPatn :: GenPatn -> RawPatn
toRawPatn = RP . fmap toRawIrrefPatn . patnOfGP

toRawIrrefPatn :: GenIrrefPatn -> RawIrrefPatn
toRawIrrefPatn = RIP . ffmap toRawIrrefPatn . fmap toRawExpr . irpatnOfGIP

toRawExpr :: GenExpr -> RawExpr
toRawExpr = RE . fffffmap toRawType . ffffmap toRawPatn . fffmap toRawIrrefPatn . ffmap toDLExpr . fmap toRawExpr . exprOfGE

toDLExpr :: () -> DataLayoutExpr
toDLExpr () = DL (LVar "")
