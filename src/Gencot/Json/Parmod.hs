{-# LANGUAGE PackageImports, TypeSynonymInstances, FlexibleInstances #-}

-- | Define JSON function descriptions.
-- A function description is represented as a JSON object and describes a function or a function pointer. 
-- It mainly consists of a description of the function parameters. 
-- For a function definition, it additionally describes all invocations of functions
-- in the function body.
module Gencot.Json.Parmod where

import Data.Map (Map)
import System.FilePath (takeExtension,takeFileName,takeBaseName)
import Text.JSON

import Language.C.Data.Ident as LCI
import Language.C.Analysis as LCA

import Gencot.Util.Types (resolveTypedef)

-- | Simplified form of evaluated function descripton sequence.
-- A mapping from function identifiers to sequences of parameter description values.
-- For every parameter the description is one of "yes", "discarded", "no", "nonlinear", or "readonly".
type ParmodMap = Map String [String]

type Parmod = JSObject JSValue
type Parmods = [Parmod]

-- | Read a sequence of function descriptions from stdin.
readParmodsFromInput :: IO Parmods
readParmodsFromInput = do
    inp <- getContents
    case decode inp of
         Ok res -> return res
         Error msg -> error msg

-- | Read a sequence of function descriptions from a file.
readParmodsFromFile :: FilePath -> IO Parmods
readParmodsFromFile file = do 
    inp <- readFile file 
    case decode inp of
         Ok res -> return res
         Error msg -> error msg

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

