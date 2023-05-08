{-# LANGUAGE PackageImports #-}
module Gencot.Cogent.Ast where

import "language-c" Language.C

import Cogent.Surface as CS (TopLevel, Expr, Pattern, IrrefutablePattern, Type(TUnit,TRecord,TArray,TCon), Binding, Alt, RawType(RT), RawPatn(RP), RawIrrefPatn(RIP), RawExpr(RE))
import Cogent.Dargent.Surface (DataLayoutExpr(DL), DataLayoutExpr'(LVar))
import Cogent.Common.Syntax (VarName)
import Cogent.Common.Types (Sigil(Boxed))
import Cogent.Util (ffmap,fffmap,ffffmap,fffffmap)

import Gencot.Origin (Origin,noOrigin)
import Gencot.C.Ast as LQ (Stm)
import Gencot.Names (mapPtrDeriv, ptrDerivCompName, isArrDeriv, arrDerivCompNam)

-- | Intermediate representation with types for expressions and patterns and with type synonyms
--------------------------------

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
    typOfGE :: GenType,
    ccdOfGE :: Maybe LQ.Stm
    } deriving (Eq, Ord, Show)
data GenPatn = GenPatn { 
    patnOfGP :: PatnOfGP,
    orgOfGP :: Origin,
    typOfGP :: GenType
    } deriving (Eq, Ord, Show)
data GenIrrefPatn = GenIrrefPatn { 
    irpatnOfGIP :: IrpatnOfGIP,
    orgOfGIP :: Origin,
    typOfGIP :: GenType
    } deriving (Eq, Ord, Show)
data GenType = GenType { 
    typeOfGT :: TypeOfGT,
    orgOfGT :: Origin,
    typSynOfGT :: Maybe String
    } deriving (Eq, Ord, Show)

-- The types Binding and Alt cannot be extended because they are used directly in Expr
-- instead of being a type parameter of Expr.
type GenBnd = CS.Binding GenType GenPatn GenIrrefPatn GenExpr
type GenAlt = CS.Alt GenPatn GenExpr

mapToplOfGTL :: (ToplOfGTL -> ToplOfGTL) -> GenToplv -> GenToplv
mapToplOfGTL f g = GenToplv (f $ toplOfGTL g) $ orgOfGTL g

mapExprOfGE :: (ExprOfGE -> ExprOfGE) -> GenExpr -> GenExpr
mapExprOfGE f g = GenExpr (f $ exprOfGE g) (orgOfGE g) (typOfGE g) (ccdOfGE g)

mapPatnOfGP :: (PatnOfGP -> PatnOfGP) -> GenPatn -> GenPatn
mapPatnOfGP f g = GenPatn (f $ patnOfGP g) (orgOfGP g) (typOfGP g)

mapIrpatnOfGIP :: (IrpatnOfGIP -> IrpatnOfGIP) -> GenIrrefPatn -> GenIrrefPatn
mapIrpatnOfGIP f g = GenIrrefPatn (f $ irpatnOfGIP g) (orgOfGIP g) (typOfGIP g)

mapTypeOfGT :: (TypeOfGT -> TypeOfGT) -> GenType -> GenType
mapTypeOfGT f g = GenType (f $ typeOfGT g) (orgOfGT g) (typSynOfGT g)

mapMExprOfGE :: Monad m => (ExprOfGE -> m ExprOfGE) -> GenExpr -> m GenExpr
mapMExprOfGE f g = do
    e' <- f $ exprOfGE g
    return $ GenExpr e' (orgOfGE g) (typOfGE g) (ccdOfGE g)

toRawType :: GenType -> RawType
toRawType = RT . fmap toRawType . ffmap toDLExpr . fffmap toRawExpr . typeOfGT

toRawPatn :: GenPatn -> RawPatn
toRawPatn = RP . fmap toRawIrrefPatn . patnOfGP

toRawIrrefPatn :: GenIrrefPatn -> RawIrrefPatn
toRawIrrefPatn = RIP . ffmap toRawIrrefPatn . fmap toRawExpr . irpatnOfGIP

toRawExpr' :: ExprOfGE -> RawExpr
toRawExpr' = RE . fffffmap toRawType . ffffmap toRawPatn . fffmap toRawIrrefPatn . ffmap toDLExpr . fmap toRawExpr

toRawExpr :: GenExpr -> RawExpr
toRawExpr = toRawExpr' . exprOfGE

toDLExpr :: () -> DataLayoutExpr
toDLExpr () = DL (LVar "")

rawToGenToplv :: TopLevel RawType RawPatn RawExpr -> GenToplv
rawToGenToplv tl = GenToplv (fmap rawToGenE $ fffmap rawToGenT $ ffmap rawToGenP tl) noOrigin

rawToGenT :: RawType -> GenType
rawToGenT (RT t) = GenType (fmap rawToGenT $ ffmap (const ()) $ fffmap rawToGenE t) noOrigin Nothing

rawToGenP :: RawPatn -> GenPatn
rawToGenP (RP p) = GenPatn (fmap rawToGenIP p) noOrigin unitType

rawToGenIP :: RawIrrefPatn -> GenIrrefPatn
rawToGenIP (RIP ip) = GenIrrefPatn (ffmap rawToGenIP $ fmap rawToGenE ip) noOrigin unitType

rawToGenE :: RawExpr -> GenExpr
rawToGenE (RE e) = GenExpr ( fffffmap rawToGenT
                           $ ffffmap  rawToGenP
                           $ fffmap   rawToGenIP
                           $ ffmap    (const ()) 
                           $ fmap     rawToGenE e) noOrigin unitType Nothing

unitType :: GenType
unitType = GenType TUnit noOrigin Nothing

-- | Target representation for code output.
--------------------------------

type ToplOfTTL = CS.TopLevel TrgType TrgPatn TrgExpr
type ExprOfTE = CS.Expr TrgType TrgPatn TrgIrrefPatn () TrgExpr
type PatnOfTP = CS.Pattern TrgIrrefPatn
type IrpatnOfTIP = CS.IrrefutablePattern VarName TrgIrrefPatn TrgExpr
type TypeOfTT = CS.Type TrgExpr () TrgType

data TrgToplv = TrgToplv {
    toplOfTTL :: ToplOfTTL,
    orgOfTTL :: Origin
    } deriving (Eq, Show)
data TrgExpr = TrgExpr {
    exprOfTE :: ExprOfTE,
    orgOfTE :: Origin,
    ccdOfTE :: Maybe LQ.Stm
    } deriving (Eq, Ord, Show)
data TrgPatn = TrgPatn {
    patnOfTP :: PatnOfTP,
    orgOfTP :: Origin
    } deriving (Eq, Ord, Show)
data TrgIrrefPatn = TrgIrrefPatn {
    irpatnOfTIP :: IrpatnOfTIP,
    orgOfTIP :: Origin
    } deriving (Eq, Ord, Show)
data TrgType = TrgType {
    typeOfTT :: TypeOfTT,
    orgOfTT :: Origin
    } deriving (Eq, Ord, Show)

-- The types Binding and Alt cannot be extended because they are used directly in Expr
-- instead of being a type parameter of Expr.
type TrgBnd = CS.Binding TrgType TrgPatn TrgIrrefPatn TrgExpr
type TrgAlt = CS.Alt TrgPatn TrgExpr

mapToplOfTTL :: (ToplOfTTL -> ToplOfTTL) -> TrgToplv -> TrgToplv
mapToplOfTTL f g = TrgToplv (f $ toplOfTTL g) $ orgOfTTL g

mapExprOfTE :: (ExprOfTE -> ExprOfTE) -> TrgExpr -> TrgExpr
mapExprOfTE f g = TrgExpr (f $ exprOfTE g) (orgOfTE g) (ccdOfTE g)

mapPatnOfTP :: (PatnOfTP -> PatnOfTP) -> TrgPatn -> TrgPatn
mapPatnOfTP f g = TrgPatn (f $ patnOfTP g) (orgOfTP g)

mapIrpatnOfTIP :: (IrpatnOfTIP -> IrpatnOfTIP) -> TrgIrrefPatn -> TrgIrrefPatn
mapIrpatnOfTIP f g = TrgIrrefPatn (f $ irpatnOfTIP g) (orgOfTIP g)

mapTypeOfTT :: (TypeOfTT -> TypeOfTT) -> TrgType -> TrgType
mapTypeOfTT f g = TrgType (f $ typeOfTT g) (orgOfTT g)
