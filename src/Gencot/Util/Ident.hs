{-# LANGUAGE PackageImports, TypeSynonymInstances, FlexibleInstances #-}
module Gencot.Util.Ident where

import Data.Maybe (catMaybes)
import "language-c" Language.C as LC
import Language.C.Data.Ident as LCI
import Language.C.Syntax.AST as LCS
import qualified Language.C.Analysis as LCA

getIdents :: [LCA.DeclEvent] -> [LCI.Ident]
getIdents l = catMaybes $ map getIdent l

getIdent :: LCA.DeclEvent -> (Maybe LCI.Ident)
getIdent (LCA.DeclEvent idec) = getDeclIdent idec
getIdent (LCA.LocalEvent idec) = getDeclIdent idec
getIdent (LCA.ParamEvent pdec) = getDeclIdent pdec
getIdent (LCA.TagEvent tdef) = getSUEIdent $ LCA.sueRef tdef
getIdent (LCA.TypeDefEvent (LCA.TypeDef res _ _ _)) = Just res
getIdent (LCA.AsmEvent _) = Nothing

getDeclIdent :: LCA.Declaration a => a -> (Maybe LCI.Ident)
getDeclIdent dec = 
    case vn of
        (LCA.VarName res _) -> Just res
        LCA.NoName -> Nothing
    where (LCA.VarDecl vn _ _) = LCA.getVarDecl dec

getSUEIdent :: LCI.SUERef -> (Maybe LCI.Ident)
getSUEIdent ref = 
    case ref of
        (LCI.NamedRef res ) -> Just res
        (LCI.AnonymousRef _) -> Nothing
