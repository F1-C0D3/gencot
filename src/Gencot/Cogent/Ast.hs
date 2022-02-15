{-# LANGUAGE PackageImports #-}
module Gencot.Cogent.Ast where

import "language-c" Language.C

import Cogent.Surface as CS (TopLevel, Expr, Pattern, IrrefutablePattern, Type, Binding, Alt, RawType(RT), RawPatn(RP), RawIrrefPatn(RIP), RawExpr(RE))
import Cogent.Dargent.Surface (DataLayoutExpr(DL), DataLayoutExpr'(LVar))
import Cogent.Common.Syntax (VarName)
import Cogent.Util (ffmap,fffmap,ffffmap,fffffmap)

import Gencot.Origin (Origin,noOrigin)
import Gencot.C.Ast as LQ (Stm)

type ToplOfGTL = CS.TopLevel GenType GenPatn GenExpr
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

mapToplOfGTL :: (ToplOfGTL -> ToplOfGTL) -> GenToplv -> GenToplv
mapToplOfGTL f g = GenToplv (f $ toplOfGTL g) $ orgOfGTL g

mapExprOfGE :: (ExprOfGE -> ExprOfGE) -> GenExpr -> GenExpr
mapExprOfGE f g = GenExpr (f $ exprOfGE g) (orgOfGE g) (ccdOfGE g)

mapPatnOfGP :: (PatnOfGP -> PatnOfGP) -> GenPatn -> GenPatn
mapPatnOfGP f g = GenPatn (f $ patnOfGP g) $ orgOfGP g

mapIrpatnOfGIP :: (IrpatnOfGIP -> IrpatnOfGIP) -> GenIrrefPatn -> GenIrrefPatn
mapIrpatnOfGIP f g = GenIrrefPatn (f $ irpatnOfGIP g) $ orgOfGIP g

mapTypeOfGT :: (TypeOfGT -> TypeOfGT) -> GenType -> GenType
mapTypeOfGT f g = GenType (f $ typeOfGT g) $ orgOfGT g

type GenBnd = CS.Binding GenType GenPatn GenIrrefPatn GenExpr
type GenAlt = CS.Alt GenPatn GenExpr

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

rawToGenToplv :: TopLevel RawType RawPatn RawExpr -> GenToplv
rawToGenToplv tl = GenToplv (fmap rawToGenE $ fffmap rawToGenT $ ffmap rawToGenP tl) noOrigin

rawToGenT :: RawType -> GenType
rawToGenT (RT t) = GenType (fmap rawToGenT $ ffmap (const ()) $ fffmap rawToGenE t) noOrigin

rawToGenP :: RawPatn -> GenPatn
rawToGenP (RP p) = GenPatn (fmap rawToGenIP p) noOrigin

rawToGenIP :: RawIrrefPatn -> GenIrrefPatn
rawToGenIP (RIP ip) = GenIrrefPatn (ffmap rawToGenIP $ fmap rawToGenE ip) noOrigin

rawToGenE :: RawExpr -> GenExpr
rawToGenE (RE e) = GenExpr ( fffffmap rawToGenT
                           $ ffffmap  rawToGenP
                           $ fffmap   rawToGenIP
                           $ ffmap    (const ()) 
                           $ fmap     rawToGenE e) noOrigin Nothing
