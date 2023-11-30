{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE PackageImports #-}
module Gencot.Cogent.Output where

import Cogent.Surface (TopLevel(FunDef), Expr(Tuple,TLApp,Put,ArrayPut), Pattern, IrrefutablePattern(PTuple), Type(TRecord,TTuple,TArray))
import Cogent.Common.Syntax (VarName)
import Cogent.Common.Types (Sigil(Unboxed),readonly)
import Cogent.PrettyPrint
import Cogent.Util (ffmap,fffmap,ffffmap,fffffmap)

import Prelude hiding ((<$>))
import Text.PrettyPrint.ANSI.Leijen

import Gencot.Origin (Origin(..),fstLine,lstLine)
import Gencot.Names (mapPtrDeriv, ptrDerivCompName, isArrDeriv, arrDerivCompNam)
import Gencot.Cogent.Ast
import Gencot.Cogent.Types (useTypeSyn)
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
    pretty (GenToplv t org) = pretty t

prettyGenTopLevels :: [GenToplv] -> Doc
prettyGenTopLevels tll = plain $ vsep $ fmap pretty tll

toTrgType :: GenType -> TrgType
toTrgType t = TrgType (fmap toTrgType $ fffmap toTrgExpr $ typeOfGT $ useTypeSyn t) $ orgOfGT t

toTrgPatn :: GenPatn -> TrgPatn
toTrgPatn p = TrgPatn (fmap toTrgIrrefPatn $ patnOfGP p) $ orgOfGP p

toTrgIrrefPatn :: GenIrrefPatn -> TrgIrrefPatn
toTrgIrrefPatn ip = TrgIrrefPatn (ffmap toTrgIrrefPatn $ fmap toTrgExpr $ irpatnOfGIP ip) $ orgOfGIP ip

toTrgExpr :: GenExpr -> TrgExpr
toTrgExpr e =  TrgExpr (fffffmap toTrgType $ ffffmap toTrgPatn $ fffmap toTrgIrrefPatn $ fmap toTrgExpr $ exprOfGE e) (orgOfGE e) $ ccdOfGE e

toTrgToplv :: GenToplv -> TrgToplv
toTrgToplv tl = TrgToplv (fffmap toTrgType $ ffmap toTrgPatn $ fmap toTrgExpr $ toplOfGTL tl) $ orgOfGTL tl

prettyTopLevels :: [GenToplv] -> Doc
prettyTopLevels tll = plain $ vsep $ fmap (pretty . toTrgToplv) tll

showCogentType :: GenType -> String
showCogentType t = (displayS $ renderCompact $ pretty $ toTrgType t) ""

instance Pretty GenType where
    -- all other type synonyms resulting from typedef names. Without type arguments.
    pretty (GenType t org (Just syn)) = lparen <> pretty syn <+> symbol "=" <+> pretty (GenType t org Nothing) <> rparen
    -- types without synonyms
    pretty (GenType t _ Nothing) = pretty t

instance TypeType GenType where
  isCon     (GenType t _ _) = isCon     t
  isTakePut (GenType t _ _) = isTakePut t
  isFun     (GenType t _ _) = isFun     t
  isAtomic  (GenType t _ _) = isAtomic  t

instance PatnType GenPatn where
  isPVar  (GenPatn p _ _) = isPVar p
  prettyP (GenPatn p _ _) = prettyP p
  prettyB (GenPatn p _ _,mt,e) = prettyB (p,mt,e)

instance Pretty GenPatn where
    pretty (GenPatn p _ _) = pretty p

instance Pretty GenIrrefPatn where
    pretty (GenIrrefPatn ip@(PTuple _) _ _) = pretty ip
    pretty (GenIrrefPatn ip _ t) = pretty ip <+> symbol "::" <+> pretty t

instance PatnType GenIrrefPatn where
  isPVar  (GenIrrefPatn ip _ _) = isPVar ip
  prettyP (GenIrrefPatn ip _ _) = prettyP ip
  prettyB (GenIrrefPatn ip@(PTuple _) _ _,mt,e) i = prettyB (ip,mt,e) i
  prettyB (GenIrrefPatn ip _ ti, Just t, e) i
    = group (pretty ip <+> symbol "::" <+> pretty ti <+> symbol ":" <+> pretty t <+> symbol "=" <+>
             (if i then (prettyPrec 100) else pretty) e)
  prettyB (GenIrrefPatn ip _ ti, Nothing, e) i
    = group (pretty ip <+> symbol "::" <+> pretty ti <+> symbol "=" <+>
             (if i then (prettyPrec 100) else pretty) e)

instance Prec GenExpr where
  prec (GenExpr e _ _ _) = prec e

instance ExprType GenExpr where
  isVar (GenExpr e _ _ _) = isVar e

instance Pretty GenExpr where
  pretty (GenExpr e@(Tuple _) _ _ _) = pretty e
  pretty (GenExpr e _ t _) = pretty e <+> symbol "::" <+> pretty t


instance Pretty TrgToplv where
    pretty (TrgToplv t@(FunDef v pt alts) org) = addOrig org $ markDef v $ pretty t
    pretty (TrgToplv t org) = addOrig org $ pretty t

instance Pretty TrgType where
    pretty (TrgType tr@(TRecord rp ts s) org) = addOrig org $ prettyTrgRT tr
    pretty (TrgType tt@(TTuple ts) org) = addOrig org $ prettyTrgRT tt
    pretty (TrgType t org) = addOrig org $ pretty t

instance TypeType TrgType where
  isCon     (TrgType t _) = isCon     t
  isTakePut (TrgType t _) = isTakePut t
  isFun     (TrgType t _) = isFun     t
  isAtomic  (TrgType t _) = isAtomic  t

prettyTrgRT :: (Type TrgExpr () TrgType) -> Doc
prettyTrgRT (TRecord rp ts s) =
    (if | s == Unboxed -> (typesymbol "#" <>)
        | readonly s -> (<> typesymbol "!")
        | otherwise -> id) $
        recordTrg (map (\(_,(b,_)) -> orgOfTT b) ts) (map (\(a,(b,_)) -> (fieldname a <+> symbol ":" <+> pretty (typeOfTT b))) ts)
prettyTrgRT (TTuple ts) = tupledTrg (map orgOfTT ts) (map (pretty.typeOfTT) ts)

recordTrg os = encloseSepOrig os (lbrace <> space) (space <> rbrace) (comma <> space)
tupledTrg os = encloseSepOrig os (lparen <> space) (space <> rparen) (comma <> space)

encloseSepOrig :: [Origin] -> Doc -> Doc -> Doc -> [Doc] -> Doc
encloseSepOrig os left right sep ds
    = case ds of
        []  -> left <> right
        [d] -> left <> addOrig (head os) d <> right
        _   -> align left <> (hcat (zipWith addOrig os (zipWith (<>) (empty : repeat sep) ds)) <> right)
--        _   -> align left <> (hcat (zipWith addOrig os (zipWith (<>) ds ((replicate ((length ds) - 1) sep) ++ [right]))))

instance PatnType TrgPatn where
  isPVar  (TrgPatn p _) = isPVar p
  prettyP (TrgPatn p _) = prettyP p
  prettyB (TrgPatn p _,mt,e) = prettyB (p,mt,e)

instance Pretty TrgPatn where
    pretty (TrgPatn p org) = addOrig org $ pretty p

instance Pretty TrgIrrefPatn where
    pretty (TrgIrrefPatn t org) = addOrig org $ pretty t

instance PatnType TrgIrrefPatn where
  isPVar  (TrgIrrefPatn p _) = isPVar p
  prettyP (TrgIrrefPatn p _) = prettyP p
  prettyB (TrgIrrefPatn p _,mt,e) = prettyB (p,mt,e)

instance Prec TrgExpr where
  prec (TrgExpr e _ _) = prec e

instance ExprType TrgExpr where
  isVar (TrgExpr e _ _) = isVar e

instance Pretty TrgExpr where
  pretty (TrgExpr e org Nothing) = addOrig org $ prettyTrgRE e
  pretty (TrgExpr e org (Just s)) = addOrig org ((prettyTrgRE e) <$> ((string . (TPM.pretty 2000) . pprCommented) s))

prettyTrgRE :: (Expr TrgType TrgPatn TrgIrrefPatn () TrgExpr) -> Doc
-- for TLApp suppress empty layout shown as {{}}
prettyTrgRE (TLApp x ts ls note) = pretty note <> varname x
                                  <> typeargs (map (\case Nothing -> symbol "_"; Just t -> pretty t) ts)
-- for Put and ArrayPut fix container precedence: change from 10 to 9 so that complex expressions are put in parentheses
prettyTrgRE (ArrayPut e es) = prettyPrec 9 e <+> symbol "@"
                            <> record (map (\(i,e) -> symbol "@" <> pretty i <+> symbol "=" <+> pretty e) es)
prettyTrgRE (Put e fs)      = prettyPrec 9 e <+> record (map handlePutAssign fs)
prettyTrgRE e = pretty e
