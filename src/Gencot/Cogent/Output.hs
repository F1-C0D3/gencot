{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PackageImports #-}
module Gencot.Cogent.Output where

import Cogent.Surface (TopLevel(FunDef), Expr, Pattern, IrrefutablePattern, Type(TRecord,TTuple,TArray))
import Cogent.Common.Syntax (VarName)
import Cogent.Common.Types (Sigil(Unboxed),readonly)
import Cogent.PrettyPrint

import Prelude hiding ((<$>))
import Text.PrettyPrint.ANSI.Leijen

import Gencot.Origin (Origin(..),fstLine,lstLine)
import Gencot.Names (mapPtrDeriv, ptrDerivCompName, isArrDeriv, arrDerivCompNam)
import Gencot.Cogent.Ast
import Gencot.C.Output (pprCommented)

import Text.PrettyPrint.Mainland.Class (ppr)
import qualified Text.PrettyPrint.Mainland as TPM (pretty,Doc,string,line,nest,text,indent)

addOrig :: Origin -> Doc -> Doc
addOrig (Origin sn en) doc =
    mark "#ORIGIN" sn fstLine
    <> doc <> 
    mark "#ENDORIG" en lstLine
    where mark marker [] ln = empty
          mark marker (on:ons) ln = (hardline <> text marker <+> cont on ln <> hardline) <> mark marker ons ln
          cont on ln = (int . ln . fst) on <> text (if snd on then " +" else "")

markDef :: String -> Doc -> Doc
markDef nam doc =
    text ("#DEF " ++ nam) <> hardline <> doc

instance Pretty GenToplv where
    pretty (GenToplv t@(FunDef v pt alts) org) = addOrig org $ markDef v $ pretty t
    pretty (GenToplv t org) = addOrig org $ pretty t

prettyTopLevels :: [GenToplv] -> Doc
prettyTopLevels tll = plain $ vsep $ fmap pretty tll

showCogent :: Pretty a => a -> String
showCogent cog = (displayS $ renderCompact $ pretty cog) ""

instance Pretty GenType where
    -- array type synonym of form CArr<size> with element type as argument
    pretty (GenType (TRecord _ [(arrx,((GenType (TArray et _ _ _) _ _),_))] _) org (Just syn))
        | isArrDeriv syn && arrDerivCompNam syn == arrx = addOrig org $ typename syn <+> hsep (map prettyT' [et])
    -- pointer type synonym CPtr with referenced type as argument
    pretty (GenType (TRecord _ [(ptrDerivCompName,(rt,_))] _) org (Just mapPtrDeriv))
        = addOrig org $ typename mapPtrDeriv <+> hsep (map prettyT' [rt])
    -- all other type synonyms resulting from typedef names. Without type arguments.
    pretty (GenType _ org (Just syn)) = addOrig org $ typename syn
    -- types without synonyms
    pretty (GenType tr@(TRecord rp ts s) org Nothing) = addOrig org $ prettyGenRT tr
    pretty (GenType tt@(TTuple ts) org Nothing) = addOrig org $ prettyGenRT tt
    pretty (GenType t org Nothing) = addOrig org $ pretty t

instance TypeType GenType where
  isCon     (GenType t _ _) = isCon     t
  isTakePut (GenType t _ _) = isTakePut t
  isFun     (GenType t _ _) = isFun     t
  isAtomic  (GenType t _ _) = isAtomic  t

prettyGenRT :: (Type GenExpr () GenType) -> Doc
prettyGenRT (TRecord rp ts s) = 
    (if | s == Unboxed -> (typesymbol "#" <>)
        | readonly s -> (<> typesymbol "!")
        | otherwise -> id) $
        recordGen (map (\(_,(b,_)) -> orgOfGT b) ts) (map (\(a,(b,_)) -> (fieldname a <+> symbol ":" <+> pretty (typeOfGT b))) ts)
prettyGenRT (TTuple ts) = tupledGen (map orgOfGT ts) (map (pretty.typeOfGT) ts)

recordGen os = encloseSepGen os (lbrace <> space) (space <> rbrace) (comma <> space)
tupledGen os = encloseSepGen os (lparen <> space) (space <> rparen) (comma <> space)

encloseSepGen :: [Origin] -> Doc -> Doc -> Doc -> [Doc] -> Doc
encloseSepGen os left right sep ds
    = case ds of
        []  -> left <> right
        [d] -> left <> addOrig (head os) d <> right
        _   -> align left <> (hcat (zipWith addOrig os (zipWith (<>) (empty : repeat sep) ds)) <> right)
--        _   -> align left <> (hcat (zipWith addOrig os (zipWith (<>) ds ((replicate ((length ds) - 1) sep) ++ [right]))))

instance PatnType GenPatn where
  isPVar  (GenPatn p _ _) = isPVar p
  prettyP (GenPatn p _ _) = prettyP p
  prettyB (GenPatn p _ _,mt,e) = prettyB (p,mt,e)

instance Pretty GenPatn where
    pretty (GenPatn p org _) = addOrig org $ pretty p

instance Pretty GenIrrefPatn where
    pretty (GenIrrefPatn t org _) = addOrig org $ pretty t

instance PatnType GenIrrefPatn where
  isPVar  (GenIrrefPatn p _ _) = isPVar p
  prettyP (GenIrrefPatn p _ _) = prettyP p
  prettyB (GenIrrefPatn p _ _,mt,e) = prettyB (p,mt,e)

instance Prec GenExpr where
  prec (GenExpr e _ _ _) = prec e

instance ExprType GenExpr where
  isVar (GenExpr e _ _ _) = isVar e

instance Pretty GenExpr where
  pretty (GenExpr e org _ Nothing) = addOrig org $ pretty e
  pretty (GenExpr e org _ (Just s)) = addOrig org ((pretty e) <$> ((string . (TPM.pretty 2000) . pprCommented) s))

