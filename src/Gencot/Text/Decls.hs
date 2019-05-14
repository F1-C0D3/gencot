{-# LANGUAGE PackageImports #-}
module Gencot.Text.Decls where

import Language.C.Data.Ident as LCI
import Language.C.Data.Node as LCN
import Language.C.Data.Position as LCP
import Language.C.Syntax.AST as LCS
import qualified Language.C.Analysis as LCA

import Gencot.Names (mapNameToLower)

transDecl :: LCA.DeclEvent -> String
transDecl (LCA.DeclEvent (LCA.Declaration (LCA.Decl (LCA.VarDecl (LCA.VarName nam _) _ _) n))) = 
    "#DECL " ++ (mapNameToLower nam) ++ " " ++ (show (LCP.posRow (LCN.posOfNode n)))
transDecl _ = ""
