{-# LANGUAGE PackageImports #-}
module Main where

import Cogent.Common.Types
import Cogent.Common.Syntax
import Cogent.Surface
import Cogent.PrettyPrint hiding (indent)

import "language-c" Language.C as LC hiding (pretty,Pretty)
import Language.C.Data.Node as LCN
import Language.C.Data.Position as LCP

import Text.PrettyPrint.ANSI.Leijen
import Prelude hiding ((<$>))
import qualified Data.Map as M

main :: IO ()
main = do
    print $ plain $ prettyTopLevels $ genSurface

genSurface :: [GenToplv]
genSurface = [
  GenToplv myorig $ AbsTypeDec "AT1" ["a", "b"] [(GenType myorig TUnit)],
  GenToplv myorig $ TypeDec "T1" ["a", "b"] (GenType myorig $ TCon "U16" [] Unboxed), 
  GenToplv myorig $ TypeDec "T2" ["a"] (GenType myorig $ TVar "a" True),
  GenToplv myorig $ TypeDec "T3" [] (GenType myorig $ TFun (GenType noorig TUnit) (GenType noorig TUnit)),
  GenToplv myorig $ TypeDec "T4" [] (GenType myorig $ TRecord [("f1", ((GenType myorig TUnit), False)),("f2", ((GenType myorig TUnit), False))] (Boxed False noRepE)),
  GenToplv myorig $ TypeDec "T5" [] (GenType noorig $ TVariant (M.insert "Tag1" ([(GenType myorig TUnit)], False) M.empty)),
  GenToplv myorig $ TypeDec "T6" [] (GenType noorig $ TTuple [(GenType noorig TUnit), (GenType noorig TUnit)]),
  GenToplv myorig $ TypeDec "T7" [] (GenType myorig $ TUnit),
  GenToplv myorig $ TypeDec "T8" [] (GenType myorig $ TUnbox   (GenType noorig TUnit)),
  GenToplv myorig $ TypeDec "T9" [] (GenType myorig $ TBang    (GenType noorig TUnit)),
  GenToplv myorig $ TypeDec "TA" [] (GenType myorig $ TTake (Just ["f1","f2"]) (GenType noorig TUnit)),
  GenToplv myorig $ TypeDec "TB" [] (GenType myorig $ TPut  (Just ["f1","f2"]) (GenType noorig TUnit)),
  GenToplv myorig $ AbsDec "af1" (PT [("t1", K True True False), ("t2", K False False False)] (GenType myorig TUnit)),
  GenToplv myorig $ FunDef "f1" (PT [("t1", K True True False)] (GenType myorig TUnit)) [
    (Alt (GenIrrefPatn myorig $ PVar "p1") Regular (FunBody $ CCont mynode))
    ],
  GenToplv myorig $ FunDef "f2" (PT [("t1", K True True False)] (GenType myorig TUnit)) [
    (Alt (GenIrrefPatn myorig $ PVar "p1") Regular (FunBody $ CCont mynode)),
    (Alt (GenIrrefPatn myorig $ PVar "p2") Regular (FunBody $ CCont mynode))
    ],
  GenToplv myorig $ ConstDef "v1" (GenType myorig TUnit) (FunBody $ CCont mynode)
  ]

data Origin = Origin (Maybe LC.NodeInfo) Bool deriving (Eq, Show)
data GenExpr = ConstExpr LC.CExpr
             | FunBody LC.CStat deriving (Show)

data GenToplv = GenToplv { orgOfTL :: Origin, toplOfGTL :: TopLevel GenType GenIrrefPatn GenExpr }  deriving (Show)
data GenIrrefPatn = GenIrrefPatn { orgOfIP :: Origin, irpatnOfGIP :: IrrefutablePattern VarName GenIrrefPatn } deriving (Show)
data GenType = GenType { orgOfT :: Origin, typeOfGT :: Type GenExpr GenType } deriving (Show)


instance Pretty GenToplv where
  pretty (GenToplv org t) = addOrig org $ pretty t

prettyTopLevels :: [GenToplv] -> Doc
prettyTopLevels tll = vsep $ fmap pretty tll

instance TypeType GenType where
  isCon     (GenType _ t) = isCon     t
  isTakePut (GenType _ t) = isTakePut t
  isFun     (GenType _ t) = isFun     t
  isAtomic  (GenType _ t) = isAtomic  t

instance Pretty GenType where
    pretty (GenType org t) = addOrig org $ pretty t

instance PatnType GenIrrefPatn where
  isPVar  (GenIrrefPatn _ p) = isPVar p
  prettyP (GenIrrefPatn _ p) = prettyP p
  prettyB (GenIrrefPatn _ p,mt,e) = prettyB (p,mt,e)

instance Pretty GenIrrefPatn where
    pretty (GenIrrefPatn org t) = addOrig org $ pretty t

instance Pretty GenExpr where
  pretty _ = empty

fstLine :: LC.NodeInfo -> Int
fstLine n = LCP.posRow $ LCN.posOfNode n

lstLine :: LC.NodeInfo -> Int
lstLine n = LCP.posRow $ fst $ LCN.getLastTokenPos n

addOrig :: Origin -> Doc -> Doc
addOrig (Origin (Just n) c) doc =
    column (\c -> (nesting (\i -> if c == 0 then nest (-i) sorig else nest (-i) (hardline <> sorig)))) <> hardline
    <> doc <> 
    column (\c -> (nesting (\i -> if c == 0 then nest (-i) eorig else nest (-i) (hardline <> eorig)))) <> hardline
--    nesting (\i -> nest (-i) (empty <$> sorig)) <$> doc <> nesting (\i -> nest (-i) (empty <$> eorig)) <$> empty
    where sorig = text "#ORIGIN" <+> (int $ fstLine n) <> cmark
          eorig = text "#ENDORIG" <+> (int $ lstLine n) <> cmark
          cmark = text (if c then " +" else "")
addOrig (Origin Nothing _) doc = doc

mypos1 = LCP.retPos $ LCP.initPos "<stdin>"
mypos2 = LCP.retPos mypos1
mynode = LCN.mkNodeInfoPosLen mypos1 (mypos2,0)
myorig = Origin (Just mynode) True
noorig = Origin Nothing False
