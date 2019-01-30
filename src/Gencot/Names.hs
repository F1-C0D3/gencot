{-# LANGUAGE PackageImports #-}
module Gencot.Names where

import Data.Char (isUpper)
import Data.Map (insert,(!))
import System.Environment (getArgs)
import System.FilePath (takeFileName, dropExtension)

import Language.C.Data.Ident as LCI
import Language.C.Data.Node as LCN
import Language.C.Data.Position as LCP
import Language.C.Analysis as LCA

import Cogent.Common.Syntax as CCS


mapName :: Bool -> LCI.Ident -> String
mapName True (LCI.Ident s _ _) = "Cogent_" ++ s
mapName False (LCI.Ident s _ _) = "cogent_" ++ s

mapNameToUpper = mapName True
mapNameToLower = mapName False

mapInternal :: String -> LCI.Ident -> String
mapInternal fnam (LCI.Ident s _ _) = "local_" ++ (dropExtension $ fnam) ++ "_" ++ s

transTagName :: LCA.GlobalDecls -> LCA.TypeName -> CCS.TypeName
transTagName g (LCA.TyComp (LCA.CompTypeRef (LCI.NamedRef idnam) kind _)) = 
    kindPrefix kind ++ mapNameToUpper idnam
    where kindPrefix LCA.StructTag = "Struct_"
          kindPrefix LCA.UnionTag  = "Union_"
transTagName g (LCA.TyComp (LCA.CompTypeRef (LCI.AnonymousRef unam) kind _)) =
    kindPrefix kind ++ show (lineNr n) ++ "_" ++ (map mapFileChar $ srcFileName g n)
    where kindPrefix LCA.StructTag = "Struct"
          kindPrefix LCA.UnionTag  = "Union"
          n = LCN.nodeInfo $ (LCA.gTags g)!(LCI.AnonymousRef unam)
transTagName g (LCA.TyEnum (LCA.EnumTypeRef (LCI.NamedRef idnam) _)) = 
    "Enum_" ++ mapNameToUpper idnam

transFunName :: LCA.GlobalDecls -> LCI.Ident -> CCS.VarName
transFunName g idnam = 
    if internalLinkage then mapInternal fnam idnam else mapNameToLower idnam
    where decdef = (LCA.gObjs g)!idnam
          fnam = srcFileName g $ LCN.nodeInfo decdef
          internalLinkage = case decdef of {
              (LCA.Declaration (LCA.Decl (LCA.VarDecl _ (LCA.DeclAttrs _ (LCA.FunLinkage LCA.InternalLinkage) _) _) _))
              -> True;
              (LCA.FunctionDef (LCA.FunDef (LCA.VarDecl _ (LCA.DeclAttrs _ (LCA.FunLinkage LCA.InternalLinkage) _) _) _ _))
              -> True;
              _ -> False
              }

transToField :: LCI.Ident -> CCS.VarName
transToField idnam = if isUpper $ head s then mapNameToLower idnam else s
    where (Ident s _ _) = idnam

mapFileChar :: Char -> Char
mapFileChar '.' = '_'
mapFileChar '-' = '_'
mapFileChar c = c

fileName :: LCN.NodeInfo -> String
fileName = takeFileName . LCP.posFile . LCN.posOfNode

lineNr :: LCN.NodeInfo -> Int
lineNr = LCP.posRow . LCN.posOfNode

srcFileName :: LCA.GlobalDecls -> LCN.NodeInfo -> String
srcFileName g n = 
    fileName $ if "<stdin>" == fileName n 
               then LCN.nodeInfo $ (LCA.gObjs g)!stdinIdent
               else n

addInputName :: GlobalDecls -> IO GlobalDecls
addInputName (GlobalDecls objs tags typedefs) = do
    args <- getArgs
    fnam <- if null args 
               then error "Error: Source file name expected as argument" 
               else return $ head args
    return $ GlobalDecls (insert stdinIdent (dummyDecl fnam) objs) tags typedefs

stdinIdent = (Ident "<stdin>" 0 undefNode)

dummyDecl :: String -> IdentDecl
dummyDecl fnam = Declaration $ Decl 
    (VarDecl NoName (DeclAttrs noFunctionAttrs NoStorage []) 
        (DirectType TyVoid noTypeQuals [])) 
        $ mkNodeInfoOnlyPos $ initPos fnam

