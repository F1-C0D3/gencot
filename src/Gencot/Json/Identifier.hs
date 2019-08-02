-- | Function identifiers used in parameter modification descriptions
module Gencot.Json.Identifier where

import System.FilePath (takeExtension,takeFileName,takeBaseName)

import Language.C.Data.Ident as LCI
import Language.C.Analysis as LCA

import Gencot.Util.Types (resolveTypedef)

-- | Construct the function identifier from a declaration and source file name
getFunId :: LCA.Declaration d => d -> String -> String
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
getGlobalNamPrefix :: LCA.Declaration d => d -> String -> String
getGlobalNamPrefix idec sfn = (linkagePrefix idec sfn False) ++ (pointerPrefix idec)

-- | Construct the name prefix for a struct member which is a function pointer (array)
getGlobalMemberPrefix :: LCI.Ident -> LCA.MemberDecl -> String
getGlobalMemberPrefix cid mdecl = (memberPrefix cid) ++ (pointerPrefix mdecl)

-- | Construct the name prefix for a typedef name for a function or function pointer (array)
getGlobalTypedefPrefix :: LCA.Type -> String
getGlobalTypedefPrefix typ = typedefPrefix ++ (pointerTypePrefix typ)

getLocalNamPrefix :: LCA.Declaration d => String -> d -> String
getLocalNamPrefix fid decl = (localPrefix fid) ++ (pointerPrefix decl)

linkagePrefix :: LCA.Declaration d => d -> String -> Bool -> String
linkagePrefix idec sfn False | isInternal idec = prefix ++ ":"
    where prefix = if (takeExtension sfn) == ".c" then (takeBaseName sfn) else (takeFileName sfn)
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
