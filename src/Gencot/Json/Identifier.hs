-- | Function identifiers used in parameter modification descriptions
module Gencot.Json.Identifier where

import System.FilePath (takeExtension,takeFileName,takeBaseName)
import Data.List (nub)

import Language.C.Data.Ident as LCI
import Language.C.Analysis as LCA
import Language.C.Data.Node as LCN

import Gencot.Util.Types (resolveTypedef,TypeCarrier,isFunction,isExtern,resolveFully,getsParmodDescr)

-- | Construct the function identifier from a declaration and source file name
getFunId :: (LCA.Declaration d, LCN.CNode d) => d -> String -> String
getFunId idec sfn = (getGlobalNamPrefix idec sfn) ++ (LCI.identToString $ LCA.declIdent idec)

-- | Construct the function identifier from a struct member
getFunMemberId :: LCI.SUERef -> LCA.MemberDecl -> String
getFunMemberId (LCI.AnonymousRef _) _ = ""
getFunMemberId (LCI.NamedRef cid) mdecl = 
    (getGlobalMemberPrefix cid mdecl) ++ (LCI.identToString $ LCA.declIdent mdecl)

-- | Construct the function identifier from a type definition
getFunTypeId :: LCA.TypeDef -> String
getFunTypeId (LCA.TypeDef idnam typ _ _) = (getGlobalTypedefPrefix typ) ++ (LCI.identToString idnam)

-- | Construct the function identifier from a function id and a local declaration
getLocalFunId :: LCA.Declaration d => String -> d -> String
getLocalFunId fid decl = (getLocalNamPrefix fid decl) ++ (LCI.identToString $ LCA.declIdent decl)

-- | Construct the name prefix for a global function or function pointer (array)
getGlobalNamPrefix :: (LCA.Declaration d, LCN.CNode d) => d -> String -> String
getGlobalNamPrefix idec sfn = (linkagePrefix idec sfn False) ++ (pointerPrefix idec)

-- | Construct the name prefix for a struct member which is a function pointer (array)
getGlobalMemberPrefix :: LCI.Ident -> LCA.MemberDecl -> String
getGlobalMemberPrefix cid mdecl = (memberPrefix cid) ++ (pointerPrefix mdecl)

-- | Construct the name prefix for a typedef name for a function or function pointer (array)
getGlobalTypedefPrefix :: LCA.Type -> String
getGlobalTypedefPrefix typ = typedefPrefix ++ (pointerTypePrefix typ)

getLocalNamPrefix :: LCA.Declaration d => String -> d -> String
getLocalNamPrefix fid decl = (localPrefix fid) ++ (pointerPrefix decl)

linkagePrefix :: (LCA.Declaration d, LCN.CNode d) => d -> String -> Bool -> String
linkagePrefix idec sfn False | isInternal idec = prefix ++ ":"
    where fn = case LCN.fileOfNode idec of
                    Nothing -> "<unknown>"
                    Just res -> takeFileName res
          fn' = if fn == "<stdin>" then sfn else fn
          prefix = if (takeExtension fn') == ".c" then (takeBaseName fn') else (takeFileName fn')
          isInternal idec = 
            case LCA.declStorage idec of
                 NoStorage -> False -- function pointer struct members
                 _ -> LCA.declLinkage idec == LCA.InternalLinkage
linkagePrefix _ _ _ = ""

localPrefix :: String -> String
localPrefix s = s ++ "/"

memberPrefix :: LCI.Ident -> String
memberPrefix (LCI.Ident idnam _ _) = idnam ++ "."

typedefPrefix :: String
typedefPrefix = "typedef|"

pointerPrefix :: LCA.Declaration d => d -> String
pointerPrefix idec = pointerTypePrefix $ LCA.declType idec

pointerTypePrefix :: LCA.Type -> String
pointerTypePrefix typ =
    case resolveTypedef typ of
         LCA.PtrType _ _ _ -> "*"
         LCA.ArrayType _ _ _ _ -> "*[]"
         _ -> ""

carriedWithFunIds :: String -> [String] -> TypeCarrier -> [(String,LCA.Type)]
carriedWithFunIds sfn _ (LCA.DeclEvent decl@(LCA.FunctionDef _)) = 
    carriedInFunction (getFunId decl sfn) $ LCA.declType decl
carriedWithFunIds sfn _ (LCA.DeclEvent decl) | isFunction $ LCA.declType decl = 
    carriedInFunction (getFunId decl sfn) $ LCA.declType decl
carriedWithFunIds sfn _ (LCA.DeclEvent decl) = [typeWithFunId (getFunId decl sfn) $ LCA.declType decl]
carriedWithFunIds _ _ (LCA.LocalEvent decl) = [("",LCA.declType decl)]
carriedWithFunIds _ _ (LCA.ParamEvent decl) = [("",LCA.declType decl)]
carriedWithFunIds _ tdn (LCA.TypeDefEvent td@(LCA.TypeDef _ t _ _)) | isExtern td = 
    [typeWithFunId (getFunTypeId td) $ resolveFully tdn t]
carriedWithFunIds _ tdn (LCA.TypeDefEvent td@(LCA.TypeDef _ t _ _)) = 
    [typeWithFunId (getFunTypeId td) t]
carriedWithFunIds _ _ (LCA.TagEvent def@(LCA.CompDef (LCA.CompType _ _ mems _ _))) = 
    nub $ map (\md -> typeWithFunId (getFunMemberId ref md) $ LCA.declType md) mems
    where ref = sueRef def
carriedWithFunIds _ _ _ = []

carriedInFunction :: String -> LCA.Type -> [(String,LCA.Type)]
carriedInFunction fid (LCA.FunctionType (LCA.FunType rt pars _) _) =
    nub (("",rt) : map (\pd -> typeWithFunId (getLocalFunId fid pd) $ LCA.declType pd) pars)
carriedInFunction fid (LCA.FunctionType (LCA.FunTypeIncomplete rt) _) = [("",rt)]
carriedInFunction _ _ = []

typeWithFunId :: String -> LCA.Type -> (String, LCA.Type)
typeWithFunId fid t | getsParmodDescr t = (fid,t)
typeWithFunId _ t = ("",t)

