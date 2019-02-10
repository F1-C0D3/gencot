{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PackageImports #-}
module Gencot.Cogent.Output where

import Cogent.Surface (TopLevel, IrrefutablePattern, Type(TRecord,TTuple))
import Cogent.Common.Syntax (VarName)
import Cogent.Common.Types (Sigil(Unboxed),readonly)
import Cogent.PrettyPrint

import Text.PrettyPrint.ANSI.Leijen

import Gencot.Origin (Origin(..),fstLine,lstLine{- -},testOrig)
import Gencot.Cogent.Ast
import qualified Gencot.C.Output as GCO

--import "language-c-quote" Language.C.Pretty
import Text.PrettyPrint.Mainland.Class (ppr)
import qualified Text.PrettyPrint.Mainland as TPM (pretty,Doc,string,line,nest,text,indent)

instance Pretty GenToplv where
  pretty (GenToplv org t) = addOrig org $ pretty t

prettyTopLevels :: [GenToplv] -> Doc
prettyTopLevels tll = plain $ vsep $ fmap pretty tll

instance Pretty GenType where
    pretty (GenType org tr@(TRecord ts s)) = addOrig org $ prettyGenRT tr 
    pretty (GenType org tt@(TTuple ts)) = addOrig org $ prettyGenRT tt
    pretty (GenType org t) = addOrig org $ pretty t

instance TypeType GenType where
  isCon     (GenType _ t) = isCon     t
  isTakePut (GenType _ t) = isTakePut t
  isFun     (GenType _ t) = isFun     t
  isAtomic  (GenType _ t) = isAtomic  t

prettyGenRT :: (Type GenExpr GenType) -> Doc
prettyGenRT (TRecord ts s) = 
    (if | s == Unboxed -> (typesymbol "#" <>)
        | readonly s -> (<> typesymbol "!")
        | otherwise -> id) $
        recordGen (map (\(_,(b,_)) -> orgOfT b) ts) (map (\(a,(b,_)) -> (fieldname a <+> symbol ":" <+> pretty (typeOfGT b))) ts)
prettyGenRT (TTuple ts) = tupledGen (map orgOfT ts) (map (pretty.typeOfGT) ts)

recordGen os = encloseSepGen os (lbrace <> space) (space <> rbrace) (comma <> space)
tupledGen os = encloseSepGen os (lparen <> space) (space <> rparen) (comma <> space)

encloseSepGen :: [Origin] -> Doc -> Doc -> Doc -> [Doc] -> Doc
encloseSepGen os left right sep ds
    = case ds of
        []  -> left <> right
        [d] -> left <> addOrig (head os) d <> right
        _   -> align left <> (hcat (zipWith addOrig os (zipWith (<>) ds ((replicate ((length ds) - 1) sep) ++ [right]))))

instance Pretty GenIrrefPatn where
    pretty (GenIrrefPatn org t) = addOrig org $ pretty t

instance PatnType GenIrrefPatn where
  isPVar  (GenIrrefPatn _ p) = isPVar p
  prettyP (GenIrrefPatn _ p) = prettyP p
  prettyB (GenIrrefPatn _ p,mt,e) = prettyB (p,mt,e)

instance Pretty GenExpr where
  pretty (ConstExpr e) = (string . (TPM.pretty 80) . ppr) e
  pretty (FunBody s) = {-hardline <>-} (string . (TPM.pretty 80) . ppr) s
{-
  pretty (ConstExpr e) = (string . show . GCO.opretty) e
  pretty (FunBody s) = {-hardline <>-} (string . show . GCO.oprettyPrec (-1)) s
-}

--cAddOrig :: Origin -> TPM.Doc -> TPM.Doc
--cAddOrig (Origin sn en) doc = TPM.line <> TPM.string "#Origin" <> TPM.line <> doc <> TPM.line <> TPM.text "#Endorig" <> TPM.line

addOrig :: Origin -> Doc -> Doc
addOrig (Origin sn en) doc =
    (if null sn then empty 
                else column (\c -> (nesting (\i -> if c == 0 then nest (-i) sorig else nest (-i) (hardline <> sorig)))) <> hardline)
    <> doc <> 
    (if null en then empty 
                else column (\c -> (nesting (\i -> if c == 0 then nest (-i) eorig else nest (-i) (hardline <> eorig)))) <> hardline)
    where sorig = text "#ORIGIN"  <+> (int . fstLine . fst . head) sn <> scmark
          eorig = text "#ENDORIG" <+> (int . lstLine . fst . head) en <> ecmark
          scmark = text (if snd $ head sn then " +" else "")
          ecmark = text (if snd $ head en then " +" else "")
--addOrig (Origin [] _ _ _) doc = doc

 
