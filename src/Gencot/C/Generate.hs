{-# LANGUAGE PackageImports #-}
module Gencot.C.Generate where

import "language-c" Language.C as LC
import Language.C.Data.Ident as LCI
import qualified Language.C.Analysis as LCA

import Gencot.C.Ast as GCA
import Gencot.Cogent.Ast (GenType)
import Gencot.Cogent.Output (showCogent)
import Gencot.Cogent.Translate (transType)

import Gencot.Origin (Origin,noOrigin,mkOrigin)
import Gencot.Names (transObjName,getFileName)
import Gencot.Traversal (FTrav)
import Gencot.Items.Types (ItemAssocType,getIndividualItemAssoc,getResultSubItemAssoc,getParamSubItemAssoc,numberList)

genEntries :: [LCA.DeclEvent] -> FTrav [GCA.Definition]
genEntries tcs = mapM genEntry tcs

genEntry :: LCA.DeclEvent -> FTrav GCA.Definition
genEntry (LCA.DeclEvent idecl@(LCA.FunctionDef fdef@(LCA.FunDef decl stat n))) = do
    f <- transObjName idnam
    sfn <- getFileName
    let iat = getIndividualItemAssoc idecl sfn
    resiat <- getResultSubItemAssoc iat
    restyp <- transType False resiat
    ps <- mapM (genParam iat) (numberList pars)
    return $ GCA.FuncDef (GCA.Func (mkADec restyp) (mkId idnam) mkRt (mkPars ps isVar) [] noOrigin) $ mkOrigin n
    where idnam = LCA.declIdent idecl
          typ@(LCA.FunctionType (LCA.FunType res pars isVar) _) = LCA.declType idecl

genParam :: ItemAssocType -> (Int,LCA.ParamDecl) -> FTrav GCA.Param
genParam fiat ipd = do
    partyp <- transType False $ getParamSubItemAssoc fiat ipd
    return $ mkPar pnam partyp
    where pnam = LCA.declIdent $ snd ipd

{-
Func 
  AntiTypeDeclSpec [] [] "<cogt0>" o
  Id "fnam" o
  DeclRoot o
  Params [Param (Just (Id "argi" o)) (AntiTypeDeclSpec "<cogti>" o) (DeclRoot o) o] False o
  [BlockStm (Return (Just (FnCall (Var (Id "cogent_fnam" o) o) [(Var (Id "arg1" o) o)] o)) o)]
  o

-}

mkId :: LCI.Ident -> GCA.Id
mkId idnam = (GCA.Id (LCI.identToString idnam) noOrigin)

mkADec :: GenType -> GCA.DeclSpec
mkADec cogtyp = (GCA.AntiTypeDeclSpec [] [] (showCogent cogtyp) noOrigin)

mkRt = GCA.DeclRoot noOrigin

mkPars :: [GCA.Param] -> Bool -> GCA.Params
mkPars [] False = GCA.Params [GCA.Param Nothing (GCA.DeclSpec [] [] (GCA.Tvoid noOrigin) noOrigin) mkRt noOrigin] False noOrigin
mkPars ps variadic = GCA.Params ps variadic noOrigin

mkPar :: LCI.Ident -> GenType -> GCA.Param
mkPar idnam partyp = GCA.Param (Just (mkId idnam)) (mkADec partyp) mkRt noOrigin


