module Main where

import Cogent.Common.Types
import Cogent.Common.Syntax
import Cogent.Surface
import Cogent.PrettyPrint

import Text.PrettyPrint.ANSI.Leijen
import Prelude hiding ((<$>))
import qualified Data.Map as M

main :: IO ()
main = do
    print $ plain $ prettyTopLevels $ genSurface

genSurface :: [RawTopLevel]
genSurface = [
  RTL $ Include    "file",
  RTL $ IncludeStd "file",
  RTL $ AbsTypeDec "AT1" ["a", "b"] [(RT TUnit)],
  RTL $ TypeDec "T1" ["a", "b"] (RT $ TCon "U16" [] Unboxed), 
  RTL $ TypeDec "T2" ["a"] (RT $ TVar "a" True),
  RTL $ TypeDec "T3" [] (RT $ TFun (RT TUnit) (RT TUnit)),
  RTL $ TypeDec "T4" [] (RT $ TRecord [("f1", ((RT TUnit), False)),("f2", ((RT TUnit), False))] (Boxed False noRepE)),
  RTL $ TypeDec "T5" [] (RT $ TVariant (M.insert "Tag1" ([(RT TUnit)], False) M.empty)),
  RTL $ TypeDec "T6" [] (RT $ TTuple [(RT TUnit), (RT TUnit)]),
  RTL $ TypeDec "T7" [] (RT $ TUnit),
  RTL $ TypeDec "T8" [] (RT $ TUnbox   (RT TUnit)),
  RTL $ TypeDec "T9" [] (RT $ TBang    (RT TUnit)),
  RTL $ TypeDec "TA" [] (RT $ TTake (Just ["f1","f2"]) (RT TUnit)),
  RTL $ TypeDec "TB" [] (RT $ TPut  (Just ["f1","f2"]) (RT TUnit)),
  RTL $ AbsDec "af1" (PT [("t1", K True True False), ("t2", K False False False)] (RT TUnit)),
  RTL $ FunDef "f1" (PT [("t1", K True True False)] (RT TUnit)) [
    (Alt (RP $ PBoolLit True) Regular (RE $ IntLit 5))
    ],
  RTL $ FunDef "f2" (PT [("t1", K True True False)] (RT TUnit)) [
    (Alt (RP $ PBoolLit True) Regular (RE $ IntLit 5)),
    (Alt (RP $ PBoolLit False) Regular (RE $ IntLit 6))
    ],
  RTL $ ConstDef "v1" (RT TUnit) (RE $ IntLit 5)
  ]

data RawTopLevel = RTL { unRTL :: TopLevel RawType RawPatn RawExpr } deriving (Eq, Show)

instance Pretty RawTopLevel where
  pretty (RTL t) = pretty t

prettyTopLevels :: [RawTopLevel] -> Doc
prettyTopLevels tll = vsep $ punctuate hardline $ fmap pretty tll
