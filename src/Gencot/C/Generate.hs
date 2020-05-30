{-# LANGUAGE PackageImports #-}
module Gencot.C.Generate where

import Data.Maybe (isNothing,fromJust)

import "language-c" Language.C as LC
import Language.C.Data.Ident as LCI
import qualified Language.C.Analysis as LCA

import Cogent.Surface (Type(TFun,TUnit,TTuple))

import Gencot.C.Ast as GCA
import Gencot.Cogent.Ast (GenType(GenType))
import Gencot.Cogent.Output (showCogent)
import Gencot.Cogent.Translate (transType)

import Gencot.Origin (Origin,noOrigin,mkOrigin)
import Gencot.Names (transObjName,getFileName)
import Gencot.Traversal (FTrav)
import Gencot.Items.Types (ItemAssocType,getIndividualItemAssoc,getResultSubItemAssoc,getParamSubItemAssoc,numberList)

genEntries :: [LCA.DeclEvent] -> FTrav [GCA.Definition]
genEntries tcs = mapM genEntry tcs

-- | Generate an entry wrapper for a function definition.
genEntry :: LCA.DeclEvent -> FTrav GCA.Definition
genEntry (LCA.DeclEvent idecl@(LCA.FunctionDef fdef@(LCA.FunDef decl stat n))) = do
    sfn <- getFileName
    let iat = getIndividualItemAssoc idecl sfn
    resiat <- getResultSubItemAssoc iat
    restyp <- transType False resiat
    let rIsVoid = case res of { (LCA.DirectType LCA.TyVoid _ _) -> True; _ -> False }
    let rspec = if rIsVoid then mkVoid else mkADec restyp
    ps <- mapM (genParam iat) numpars
    bdy <- genBody iat numpars idnam rIsVoid
    return $ GCA.FuncDef (GCA.Func rspec (mkId idnam) mkRt (mkPars ps isVar) bdy noOrigin) $ mkOrigin n
    where idnam = LCA.declIdent idecl
          typ@(LCA.FunctionType (LCA.FunType res pars isVar) _) = LCA.declType idecl
          numpars = numberList pars

-- | Generate a parameter declaration for a formal parameter of the wrapper.
-- As identifier it uses the same name as the original parameter in the function definition.
-- As type it uses the antiquoted Cogent type translated from the original parameter type.
genParam :: ItemAssocType -> (Int,LCA.ParamDecl) -> FTrav GCA.Param
genParam fiat ipd = do
    partyp <- transType False $ getParamSubItemAssoc fiat ipd
    return $ mkPar pnam partyp
    where pnam = LCA.declIdent $ snd ipd

-- | Generate the wrapper body.
-- It consists of a definition of the parameter tuple or the unit value, if necessary,
-- the invocation of the wrapped Cogent function
-- and the retrieval of the return value from the result tuple, if necessary.
genBody :: ItemAssocType -> [(Int,LCA.ParamDecl)] -> LCI.Ident -> Bool -> FTrav [GCA.BlockItem]
genBody fiat numpars idnam rIsVoid = do
    f <- transObjName idnam
    cogtyp <- transType False fiat
    let (cogptyp,cogrtyp) = case cogtyp of {
        (GenType (TFun p r) _) -> (p,r);
        _ -> (GenType TUnit noOrigin, GenType TUnit noOrigin) }
    let (aarg,aval) = case cogptyp of {
        (GenType TUnit _) -> ("arg", (Just mkUVal));
        (GenType (TTuple cogptypes) _) -> ("arg", (Just $ mkTVal numpars));
        _ -> (LCI.identToString $ LCA.declIdent $ snd $ head numpars, Nothing) }
    let invk = mkInvk f aarg
    let rval = case cogrtyp of {
        (GenType TUnit _) -> Nothing;
        (GenType (TTuple cogptypes) _) -> (Just $ mkMbAcc invk "p1");
        _ -> (Just invk) }
    let rstat = if rIsVoid then mkSStm invk else mkRet $ fromJust rval
    return (if isNothing aval then [rstat] else [mkArgDef cogptyp $ fromJust aval , rstat])


{- 
  GenType (CS.TFun (GenType (CS.TUnit) o) rt) o
  GenType (CS.TFun (GenType (CS.TTuple [pt1 ... ptn]) o) rt) o
  GenType (CS.TFun pt1 rt) o

Func 
  AntiTypeDeclSpec [] [] "<cogt0>" o
  Id "fnam" o
  DeclRoot o
  Params [Param (Just (Id "argi" o)) (AntiTypeDeclSpec "<cogti>" o) (DeclRoot o) o] False o
  [BlockStm (Return (Just (FnCall (Var (Id "cogent_fnam" o) o) [(Var (Id "arg1" o) o)] o)) o)]
  o

-}

-- | Generate idnam
mkId :: LCI.Ident -> GCA.Id
mkId idnam = (GCA.Id (LCI.identToString idnam) noOrigin)

-- | Generate nam
mkVar :: String -> GCA.Exp
mkVar nam = (GCA.Var (GCA.Id nam noOrigin) noOrigin)

-- | Generate i
mkIConst :: Integer -> GCA.Exp
mkIConst i = (GCA.Const (GCA.IntConst "" Signed i noOrigin) noOrigin)

-- | Generate $ty:(cogtyp)
mkADec :: GenType -> GCA.DeclSpec
mkADec cogtyp = (GCA.AntiTypeDeclSpec [] [] (showCogent cogtyp) noOrigin)

-- | Generate void
mkVoid :: GCA.DeclSpec
mkVoid = (GCA.DeclSpec [] [] (GCA.Tvoid noOrigin) noOrigin)

-- | Generate (void) or (pd1, ... ,pdn [,...])
mkPars :: [GCA.Param] -> Bool -> GCA.Params
mkPars [] False = GCA.Params [GCA.Param Nothing mkVoid mkRt noOrigin] False noOrigin
mkPars ps variadic = GCA.Params ps variadic noOrigin

-- | Generate $ty:(partyp) idnam
mkPar :: LCI.Ident -> GenType -> GCA.Param
mkPar idnam partyp = GCA.Param (Just (mkId idnam)) (mkADec partyp) mkRt noOrigin

-- | Generate {.dummy=0}
mkUVal :: GCA.Initializer 
mkUVal = GCA.CompoundInitializer [mkMbInit "dummy" $ mkIConst 0] noOrigin

-- | Generate {.p1=<pname1>, ..., .pn=<pnamen>}
mkTVal :: [(Int,LCA.ParamDecl)] -> GCA.Initializer
mkTVal numpars = GCA.CompoundInitializer (map mkTInit numpars) noOrigin

-- | Generate .p<pos>=<pd-name>
mkTInit :: (Int,LCA.ParamDecl) -> (Maybe GCA.Designation, GCA.Initializer)
mkTInit (pos,pd) = mkMbInit ("p" ++ (show pos)) $ mkVar $ LCI.identToString $ LCA.declIdent pd

-- | Generate .nam=val
mkMbInit :: String -> GCA.Exp -> (Maybe GCA.Designation, GCA.Initializer)
mkMbInit nam val = 
    ((Just (GCA.Designation [GCA.MemberDesignator (GCA.Id nam noOrigin) noOrigin] noOrigin)),
     (GCA.ExpInitializer val noOrigin))

-- | Generate $ty:(cogtyp) arg = ini;
mkArgDef :: GenType -> GCA.Initializer -> GCA.BlockItem
mkArgDef cogtyp ini = 
    GCA.BlockDecl $ GCA.InitGroup (mkADec cogtyp) [] 
        [GCA.Init (GCA.Id "arg" noOrigin) mkRt Nothing (Just ini) [] noOrigin ] noOrigin

-- | Generate fnam(pnam)
mkInvk :: String -> String -> GCA.Exp
mkInvk fnam pnam = (GCA.FnCall (mkVar fnam) [mkVar pnam] noOrigin)

-- | Generate strct.memb
mkMbAcc :: GCA.Exp -> String -> GCA.Exp
mkMbAcc strct memb = GCA.Member strct (GCA.Id memb noOrigin) noOrigin

-- | Generate return e;
mkRet :: GCA.Exp -> GCA.BlockItem
mkRet e = GCA.BlockStm $ GCA.Return (Just e) noOrigin

-- | Generate e;
mkSStm :: GCA.Exp -> GCA.BlockItem
mkSStm e = GCA.BlockStm $ GCA.Exp (Just e) noOrigin

mkRt = GCA.DeclRoot noOrigin

{-
BlockDecl
  InitGroup (AntiTypeDeclSpec "<cogptyp>" o) [] 
    [Init (Id "arg" o) (DeclRoot o) Nothing 
      (Just (CompoundInitializer [((Just (Designation [MemberDesignator (Id "pi" o) o] o)), (ExpInitializer (Var (Id "<argi>" o) o) o))]       (Just (CompoundInitializer [((Just (Designation [MemberDesignator (Id "dummy" o) o] o)), (ExpInitializer (Const (IntConst         "" True 0 o) o) o))] o)) 
      [] o] 
    o
  o
  -}
