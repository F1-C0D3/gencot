{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PackageImports #-}
module Gencot.Cogent.Output where

import Cogent.Surface (TopLevel, IrrefutablePattern, Type(TRecord,TTuple))
import Cogent.Common.Syntax (VarName)
import Cogent.Common.Types (Sigil(Unboxed),readonly)
import Cogent.PrettyPrint

import Prelude hiding ((<$>))
import Text.PrettyPrint.ANSI.Leijen

import Gencot.Origin (Origin(..),fstLine,lstLine)
import Gencot.Cogent.Ast
import Gencot.C.Output (pprCommented)

import Text.PrettyPrint.Mainland.Class (ppr)
import qualified Text.PrettyPrint.Mainland as TPM (pretty,Doc,string,line,nest,text,indent)

addOrig :: Origin -> Doc -> Doc
addOrig (Origin sn en) doc =
    mark "#ORIGIN" sn fstLine
    <> doc <> 
    mark "#ENDORIG" en lstLine
    where mark marker ons ln = 
              if null ons then empty 
                          else (hardline <> text marker <+> cont ons ln <> hardline)
          cont ons ln = (int . ln . fst . head) ons <> text (if snd $ head ons then " +" else "")
 
instance Pretty GenToplv where
  pretty (GenToplv t org) = addOrig org $ pretty t

prettyTopLevels :: [GenToplv] -> Doc
prettyTopLevels tll = plain $ vsep $ fmap pretty tll

instance Pretty GenType where
    pretty (GenType tr@(TRecord ts s) org) = addOrig org $ prettyGenRT tr 
    pretty (GenType tt@(TTuple ts) org) = addOrig org $ prettyGenRT tt
    pretty (GenType t org) = addOrig org $ pretty t

instance TypeType GenType where
  isCon     (GenType t _) = isCon     t
  isTakePut (GenType t _) = isTakePut t
  isFun     (GenType t _) = isFun     t
  isAtomic  (GenType t _) = isAtomic  t

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
        _   -> align left <> (hcat (zipWith addOrig os (zipWith (<>) (empty : repeat sep) ds)) <> right)
--        _   -> align left <> (hcat (zipWith addOrig os (zipWith (<>) ds ((replicate ((length ds) - 1) sep) ++ [right]))))

instance Pretty GenIrrefPatn where
    pretty (GenIrrefPatn t org) = addOrig org $ pretty t

instance PatnType GenIrrefPatn where
  isPVar  (GenIrrefPatn p _) = isPVar p
  prettyP (GenIrrefPatn p _) = prettyP p
  prettyB (GenIrrefPatn p _,mt,e) = prettyB (p,mt,e)

instance Pretty GenExpr where
  pretty (ConstExpr e) = (string . (TPM.pretty 2000) . ppr) e
  pretty (FunBody d s) = (pretty d) <$> ((string . (TPM.pretty 2000) . pprCommented) s)

