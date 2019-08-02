{-# LANGUAGE PackageImports #-}
module Gencot.Util.Functions where

import Data.Maybe (catMaybes)
import Data.List (nub)

import "language-c" Language.C as LC
import Language.C.Data.Ident as LCI
import Language.C.Syntax.AST as LCS
import qualified Language.C.Analysis as LCA

import Gencot.Util.Types (TypeSet,isFunction,getFunType,getsParmodDescr,selInFunction,isPrimitive)

-- | For every function declaration determine all parameters of function (pointer (array)) type
-- where the derived function type is directly specified in the parameter declaration.
-- Input declarations are associated with a function id. This id is transferred to all its parameters.
getFunctionPars :: [(String,LCA.IdentDecl)] -> [(String,LCA.ParamDecl)]
getFunctionPars decls = concat $ map getFunPars decls

getFunPars :: (String,LCA.IdentDecl) -> [(String,LCA.ParamDecl)]
getFunPars (fid,decl) | isFunction typ =
    let ftyp = getFunType typ in
        case ftyp of
             LCA.FunType _ pars _ -> catMaybes $ map mkFunPar pars
             LCA.FunTypeIncomplete _ -> []
    where typ = LCA.declType decl
          mkFunPar pdecl = 
              if getsParmodDescr $ LCA.declType pdecl
                 then Just (fid,pdecl)
                 else Nothing
getFunPars _ = []

{-
-- | For every function declaration determine all non-primitive parameter and result types.
getParameterResultTypes :: [LCA.IdentDecl] -> TypeSet
getParameterResultTypes decls = nub $ concat $ map getParResTypes decls

getParResTypes :: LCA.IdentDecl -> TypeSet
getParResTypes (LCA.Declaration decl) =
    selInFunction (not . isPrimitive) $ LCA.declType decl
getParResTypes _ = []
-}
