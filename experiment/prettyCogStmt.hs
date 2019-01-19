module Main where

import Cogent.Common.Types
import Cogent.Common.Syntax
import Cogent.Surface
import Cogent.PrettyPrint

import qualified Language.C as LC 
import Language.C.Data.Node as LCN
import Language.C.Data.Position as LCP

--import qualified Text.PrettyPrint.HughesPJ as PPH (Doc)

import Text.PrettyPrint.ANSI.Leijen as PPL hiding (indent, tupled) -- Cogent.PrettyPrint defines own indent, tupled
import Prelude hiding ((<$>))
import qualified Data.Map as M

main :: IO ()
main = do
    print $ plain $ prettyTopLevels $ genSurface

genSurface :: [NodeTopLevel]
genSurface = [
  NTL (Just mynode) $ CogTopLev $ AbsTypeDec "AT1" ["a", "b"] [(NT (Just mynode) TUnit)],
  NTL (Just mynode) $ CogTopLev $ TypeDec "T1" ["a", "b"] (NT (Just mynode) $ TCon "U16" [] Unboxed), 
  NTL (Just mynode) $ CogTopLev $ TypeDec "T2" ["a"] (NT (Just mynode) $ TVar "a" True),
  NTL (Just mynode) $ CogTopLev $ TypeDec "T3" [] (NT (Just mynode) $ TFun (NT Nothing TUnit) (NT Nothing TUnit)),
  NTL (Just mynode) $ CogTopLev $ TypeDec "T4" [] (NT (Just mynode) $ TRecord [("f1", ((NT (Just mynode) TUnit), False)),("f2", ((NT (Just mynode) TUnit), False))] (Boxed False noRepE)),
  NTL (Just mynode) $ CogTopLev $ TypeDec "T5" [] (NT Nothing $ TVariant (M.insert "Tag1" ([(NT (Just mynode) TUnit)], False) M.empty)),
  NTL (Just mynode) $ CogTopLev $ TypeDec "T6" [] (NT Nothing $ TTuple [(NT Nothing TUnit), (NT Nothing TUnit)]),
  NTL (Just mynode) $ CogTopLev $ TypeDec "T7" [] (NT (Just mynode) $ TUnit),
  NTL (Just mynode) $ CogTopLev $ TypeDec "T8" [] (NT (Just mynode) $ TUnbox   (NT Nothing TUnit)),
  NTL (Just mynode) $ CogTopLev $ TypeDec "T9" [] (NT (Just mynode) $ TBang    (NT Nothing TUnit)),
  NTL (Just mynode) $ CogTopLev $ TypeDec "TA" [] (NT (Just mynode) $ TTake (Just ["f1","f2"]) (NT Nothing TUnit)),
  NTL (Just mynode) $ CogTopLev $ TypeDec "TB" [] (NT (Just mynode) $ TPut  (Just ["f1","f2"]) (NT Nothing TUnit)),
  NTL (Just mynode) $ CogTopLev $ AbsDec "af1" (PT [("t1", K True True False), ("t2", K False False False)] (NT (Just mynode) TUnit)),
  NTL (Just mynode) $ CogTopLev $ FunDef "f1" (PT [("t1", K True True False)] (NT (Just mynode) TUnit)) [
    (Alt (RP $ PBoolLit True) Regular (RE $ IntLit 5))
    ],
  NTL (Just mynode) $ CogTopLev $ FunDef "f2" (PT [("t1", K True True False)] (NT (Just mynode) TUnit)) [
    (Alt (RP $ PBoolLit True) Regular (RE $ IntLit 5)),
    (Alt (RP $ PBoolLit False) Regular (RE $ IntLit 6))
    ],
  NTL (Just mynode) $ HybFunDef "f3" (PT [("t1", K False False False)] (NT Nothing TUnit)) ["p1", "p2", "p3"] (LC.CBreak mynode),
  NTL (Just mynode) $ CogTopLev $ ConstDef "v1" (NT (Just mynode) TUnit) (RE $ IntLit 5)
  ]

data ExtTopLevel t p e = CogTopLev (TopLevel t p e)
                       | HybFunDef VarName (Polytype t) [VarName] LC.CStat

instance (Pretty t, Pretty p, Pretty e)  => Pretty (ExtTopLevel t p e) where
  pretty (CogTopLev t) = pretty t
  pretty (HybFunDef nam pt args body) = prettyHybFunDef nam pt args body

prettyHybFunDef :: Pretty t => FunName -> Polytype t -> [VarName] -> LC.CStat -> Doc
prettyHybFunDef v pt args body = 
    (funname v <+> symbol ":" <+> pretty pt <$>)
      (funname v <+> (tupled $ fmap pretty args) <+> group (indent (symbol "=" <$> (string . show . LC.pretty) body)))

data NodeTopLevel = NTL { nodeOfNTL :: Maybe LC.NodeInfo, toplevelOfNTL :: ExtTopLevel NodeType RawPatn RawExpr }

instance Pretty NodeTopLevel where
  pretty (NTL (Just n) t) = addOrig n $ pretty t
  pretty (NTL Nothing t) = pretty t

prettyTopLevels :: [NodeTopLevel] -> Doc
prettyTopLevels tll = vsep $ fmap pretty tll

data NodeType = NT { nodeOfNT :: Maybe LC.NodeInfo, typeOfNT :: Type RawExpr NodeType }

instance TypeType NodeType where
  isCon     (NT _ t) = isCon     t
  isTakePut (NT _ t) = isTakePut t
  isFun     (NT _ t) = isFun     t
  isAtomic  (NT _ t) = isAtomic  t

instance Pretty NodeType where
  pretty (NT (Just n) t) = addOrig n $ pretty t
  pretty (NT Nothing t) = pretty t

fstLine :: LC.NodeInfo -> Int
fstLine n = LCP.posRow $ LCN.posOfNode n

lstLine :: LC.NodeInfo -> Int
lstLine n = LCP.posRow $ fst $ LCN.getLastTokenPos n

addOrig :: LC.NodeInfo -> Doc -> Doc
addOrig n doc = empty <$> text "#ORIGIN" <+> (int $ fstLine n) <$> doc <$> text "#ENDORIG" <+> (int $ lstLine n) <$> empty

mypos1 = LCP.retPos $ LCP.initPos "<stdin>"
mypos2 = LCP.retPos mypos1
mynode = LCN.mkNodeInfoPosLen mypos1 (mypos2,0)


