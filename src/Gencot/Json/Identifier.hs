-- | Function identifiers used in parameter modification descriptions
module Gencot.Json.Identifier where

import System.FilePath (takeExtension,takeFileName,takeBaseName)

import Language.C.Data.Ident as LCI
import Language.C.Analysis as LCA

import Gencot.Util.Types (resolveTypedef)

-- | Construct the function identifier from a declaration and source file name
getFunId :: LCA.Declaration d => d -> String -> String
getFunId idec sfn = (getGlobalNamPrefix idec sfn) ++ (LCI.identToString $ LCA.declIdent idec)

-- | Construct the name prefix for a global function or function pointer
getGlobalNamPrefix :: LCA.Declaration d => d -> String -> String
getGlobalNamPrefix idec sfn = (linkagePrefix idec sfn False) ++ (pointerPrefix idec)

-- | Construct the name prefix for a struct member which is a function pointer 
getGlobalMemberPrefix :: LCI.Ident -> LCA.MemberDecl -> String
getGlobalMemberPrefix cid mdecl = (memberPrefix cid) ++ (pointerPrefix mdecl)

linkagePrefix :: LCA.Declaration d => d -> String -> Bool -> String
linkagePrefix idec sfn False | isInternal idec = prefix ++ ":"
    where prefix = if (takeExtension sfn) == ".c" then (takeBaseName sfn) else (takeFileName sfn)
          isInternal idec = 
            case LCA.declStorage idec of
                 NoStorage -> False -- function pointer struct members
                 _ -> LCA.declLinkage idec == LCA.InternalLinkage
linkagePrefix _ _ _ = ""

memberPrefix :: LCI.Ident -> String
memberPrefix (LCI.Ident idnam _ _) = idnam ++ "."

pointerPrefix :: LCA.Declaration d => d -> String
pointerPrefix idec = 
    case resolveTypedef $ LCA.declType idec of
         LCA.PtrType _ _ _ -> "*"
         _ -> ""

