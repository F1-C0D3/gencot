{-# LANGUAGE PackageImports #-}
module Gencot.C.Generate where

import Data.Maybe (isNothing,fromJust)
import Data.List (sort,break)
import Control.Monad (liftM)

import "language-c" Language.C as LC
import Language.C.Data.Ident as LCI
import qualified Language.C.Analysis as LCA

import Cogent.Surface (Type(TFun,TUnit,TTuple))

import Gencot.C.Ast as GCA
import Gencot.C.Translate (transInit)
import Gencot.Cogent.Ast (GenType(GenType))
import Gencot.Cogent.Output (showCogent)
import Gencot.Cogent.Translate (transType)

import Gencot.Origin (Origin,noOrigin,mkOrigin)
import Gencot.Names (transObjName,getFileName,mapInternal)
import Gencot.Traversal (FTrav)
import Gencot.Items.Types (ItemAssocType,getIndividualItemAssoc,getResultSubItemAssoc,getParamSubItemAssoc,getGlobalStateSubItemIds,getGlobalStateProperty,getGlobalStateId,numberList)

genEntries :: [LCA.DeclEvent] -> FTrav [GCA.Definition]
genEntries tcs = mapM genEntry tcs

-- | Generate entry wrappers and global variable definitions.
genEntry :: LCA.DeclEvent -> FTrav GCA.Definition
-- Generate an entry wrapper for a function definition.
genEntry (LCA.DeclEvent idecl@(LCA.FunctionDef fdef@(LCA.FunDef decl stat n))) = do
    sfn <- getFileName
    let iat = getIndividualItemAssoc idecl sfn
    --_ <- if "main" == (fst iat) then error ("genEntry: " ++ (fst iat)) else return ()
    resiat <- getResultSubItemAssoc iat
    restyp <- transType False resiat
    let rIsVoid = case res of { (LCA.DirectType LCA.TyVoid _ _) -> True; _ -> False }
    let rspec = if rIsVoid then mkVoid else mkADec restyp
    ps <- mapM (genParam iat) numpars
    bdy <- genBody iat numpars idnam rIsVoid
    return $ GCA.FuncDef (mkFunDef rspec (LCI.identToString idnam) ps isVar bdy) $ mkOrigin n
    where idnam = LCA.declIdent idecl
          typ@(LCA.FunctionType (LCA.FunType res pars isVar) _) = LCA.declType idecl
          numpars = numberList pars
-- Convert a variable definition.
-- The type is converted to the antiquoted translated type.
-- In case of internal linkage the name is converted to make it unique.
genEntry (LCA.DeclEvent odef@(LCA.ObjectDef (LCA.ObjDef _ minit n))) = do
    sfn <- getFileName
    let iat = getIndividualItemAssoc odef sfn
    t <- transType False iat
    mini <- mapM transInit minit
    return $ GCA.DecDef (mkObjDef t (isStatic,isConst) (getObjName $ fst iat) mini) $ mkOrigin n
    where isStatic = (LCA.declLinkage odef) == LCA.InternalLinkage
          isConst = LCA.constant $ qual $ LCA.declType odef
          qual (LCA.DirectType _ tq _) = tq
          qual (LCA.PtrType _ tq _) = tq
          qual (LCA.ArrayType _ _ tq _) = tq
          qual (LCA.FunctionType _ _) = LCA.noTypeQuals
          qual (LCA.TypeDefType _ tq _) = tq

-- | Generate a parameter declaration for a formal parameter of the wrapper.
-- As identifier it uses the same name as the original parameter in the function definition.
-- As type it uses the antiquoted Cogent type translated from the original parameter type.
genParam :: ItemAssocType -> (Int,LCA.ParamDecl) -> FTrav GCA.Param
genParam fiat ipd = do
    partyp <- transType False $ getParamSubItemAssoc fiat ipd
    return $ mkPar pnam partyp
    where pnam = LCI.identToString $ LCA.declIdent $ snd ipd

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
        _ -> error "Function has no function type" }
    gsinits <- genGSInits fiat $ (1 + length numpars) -- [.pn+1=&gvar1,...]
    let inits = ainits ++ gsinits
    let (aarg,aval) = case length inits of {
        0 -> (mkVar "arg", (Just mkUVal));
        1 -> (getInitVal inits, Nothing);
        _ -> (mkVar "arg", (Just $ mkTVal inits)) }
    let invk = mkInvk f aarg
    let rval = case cogrtyp of {
        (GenType TUnit _) -> Nothing;
        (GenType (TTuple cogptypes) _) -> (Just $ mkMbAcc invk "p1");
        _ -> (Just invk) }
    let rstat = if rIsVoid then mkSStm invk else mkRet $ fromJust rval
    return (if isNothing aval then [rstat] else [mkArgDef cogptyp $ fromJust aval , rstat])
    where ainits = map mkTInit numpars  -- [.p1=<pname1>,...]

-- | Generate the list of initializations for virtual parameters with Global-State property.
-- The first argument is the item associated type of the function.
-- The second argument is the position to be used for the first virtual parameter.
genGSInits :: ItemAssocType -> Int -> FTrav [(Maybe GCA.Designation, GCA.Initializer)]
genGSInits fiat pos = do
    vpars <- getGlobalStateSubItemIds fiat
    gsps <- mapM getGlobalStateProperty vpars
    gvars <- mapM getGlobalStateId $ sort gsps
    return $ map mkRefInit $ zip (iterate (1 +) pos) $ map getObjName gvars
    
-- | Convert a toplevel item identifier to a C identifier.
-- For items with internal linkage the mapped C identifier is returned, otherwise the original C identifier is returned.
getObjName :: String -> String
getObjName iid = 
    if null pst then iid else mapInternal pre (LCI.Ident (tail pst) 0 LC.undefNode)
    where (pre,pst) = break (== ':') iid


{- 
  GenType (CS.TFun (GenType (CS.TUnit) o) rt) o
  GenType (CS.TFun (GenType (CS.TTuple [pt1 ... ptn]) o) rt) o
  GenType (CS.TFun pt1 rt) o

FuncDef
Func 
  AntiTypeDeclSpec [] [] "<cogt0>" o
  Id "fnam" o
  DeclRoot o
  Params [Param (Just (Id "argi" o)) (AntiTypeDeclSpec "<cogti>" o) (DeclRoot o) o] False o
  [BlockStm (Return (Just (FnCall (Var (Id "cogent_fnam" o) o) [(Var (Id "arg1" o) o)] o)) o)]
  o
o

DecDef
InitGroup
  AntiTypeDeclSpec [Tstatic | Textern Nothing] [Tconst] "<cogt>" o
  [] 
  [Init (Id "name" o) (DeclRoot o) Nothing (Maybe Initializer) [] o]
  o
o
-}

-- | Generate nam
mkId :: String -> GCA.Id
mkId nam = (GCA.Id nam noOrigin)

-- | Generate nam
mkVar :: String -> GCA.Exp
mkVar nam = (GCA.Var (mkId nam) noOrigin)

-- | Generate i
mkIConst :: Integer -> GCA.Exp
mkIConst i = (GCA.Const (GCA.IntConst "" Signed i noOrigin) noOrigin)

-- | Generate $ty:(cogtyp)
mkADec :: GenType -> GCA.DeclSpec
mkADec cogtyp = mkADecSpec cogtyp (False,False)

-- | Generate [static] [const] $ty:(cogtyp)
mkADecSpec :: GenType -> (Bool,Bool) -> GCA.DeclSpec
mkADecSpec cogtyp (isStatic,isConst) = (GCA.AntiTypeDeclSpec extsta cst (showCogent cogtyp) noOrigin)
    where cst = if isConst then [GCA.Tconst noOrigin] else []
          extsta = if isStatic then [GCA.Tstatic noOrigin] else []

-- | Generate void
mkVoid :: GCA.DeclSpec
mkVoid = (GCA.DeclSpec [] [] (GCA.Tvoid noOrigin) noOrigin)

-- | Generate (void) or (pd1, ... ,pdn [,...])
mkPars :: [GCA.Param] -> Bool -> GCA.Params
mkPars [] False = GCA.Params [GCA.Param Nothing mkVoid mkRt noOrigin] False noOrigin
mkPars ps variadic = GCA.Params ps variadic noOrigin

-- | Generate $ty:(partyp) nam
mkPar :: String -> GenType -> GCA.Param
mkPar nam partyp = GCA.Param (Just (mkId nam)) (mkADec partyp) mkRt noOrigin

-- | Generate {.dummy=0}
mkUVal :: GCA.Initializer 
mkUVal = GCA.CompoundInitializer [mkMbInit "dummy" $ mkIConst 0] noOrigin

-- | Generate {.nam1=val1, ..., .namn=valn}
mkTVal :: [(Maybe GCA.Designation, GCA.Initializer)] -> GCA.Initializer
mkTVal inits = GCA.CompoundInitializer inits noOrigin

-- | Retrieve val from [.nam=val]
getInitVal :: [(Maybe GCA.Designation, GCA.Initializer)] -> GCA.Exp 
getInitVal [(_,(GCA.ExpInitializer e _))] = e
getInitVal _ = error "no Expr found in initializer"

-- | Generate .p<pos>=<pd-name>
mkTInit :: (Int,LCA.ParamDecl) -> (Maybe GCA.Designation, GCA.Initializer)
mkTInit (pos,pd) = mkMbInit ("p" ++ (show pos)) $ mkVar $ LCI.identToString $ LCA.declIdent pd

mkRefInit :: (Int,String) -> (Maybe GCA.Designation, GCA.Initializer)
mkRefInit (pos,nam) = mkMbInit ("p" ++ (show pos)) $ mkRef $ mkVar nam

-- | Generate .nam=val
mkMbInit :: String -> GCA.Exp -> (Maybe GCA.Designation, GCA.Initializer)
mkMbInit nam val = 
    ((Just (GCA.Designation [GCA.MemberDesignator (mkId nam) noOrigin] noOrigin)),
     (GCA.ExpInitializer val noOrigin))

-- | Generate rtyp nam(pars [...]) { body }
mkFunDef :: GCA.DeclSpec -> String -> [GCA.Param] -> Bool -> [GCA.BlockItem] -> GCA.Func
mkFunDef rspec nam pars isVar body =
    GCA.Func rspec (mkId nam) mkRt (mkPars pars isVar) body noOrigin

-- | Generate [static] [const] $ty:(cogtyp) <nam> [= <initializer>];
mkObjDef :: GenType -> (Bool,Bool) -> String -> (Maybe GCA.Initializer) -> GCA.InitGroup
mkObjDef cogtyp (isStatic,isConst) nam mini =
    GCA.InitGroup (mkADecSpec cogtyp (isStatic,isConst)) [] [mkDef nam mini] noOrigin

-- | Generate $ty:(cogtyp) arg = ini;
mkArgDef :: GenType -> GCA.Initializer -> GCA.BlockItem
mkArgDef cogtyp ini = 
    GCA.BlockDecl $ GCA.InitGroup (mkADec cogtyp) [] [mkDef "arg" (Just ini)] noOrigin

-- | Generate <nam> [= <initializer>]
mkDef :: String -> (Maybe GCA.Initializer) -> GCA.Init
mkDef nam mini = GCA.Init (mkId nam) mkRt Nothing mini [] noOrigin

-- | Generate fnam(pnam)
mkInvk :: String -> GCA.Exp -> GCA.Exp
mkInvk fnam arg = (GCA.FnCall (mkVar fnam) [arg] noOrigin)

-- | Generate strct.memb
mkMbAcc :: GCA.Exp -> String -> GCA.Exp
mkMbAcc strct memb = GCA.Member strct (mkId memb) noOrigin

-- | Generate &e
mkRef :: GCA.Exp -> GCA.Exp
mkRef e = GCA.UnOp GCA.AddrOf e noOrigin

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
