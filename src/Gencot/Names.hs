{-# LANGUAGE PackageImports #-}
module Gencot.Names where

import Data.Char (isUpper)
import Data.List (isPrefixOf)
import System.Environment (getArgs)
import System.FilePath (takeFileName, dropExtension)

import Language.C.Data.Ident as LCI
import Language.C.Data.Node as LCN
import Language.C.Data.Position as LCP
import Language.C.Analysis as LCA
import Language.C.Analysis.DefTable as LCD

import Cogent.Common.Syntax as CCS

mapName :: Bool -> LCI.Ident -> String
mapName True (LCI.Ident s _ _) = 
    if "mbedtls_" `isPrefixOf` s 
       then "Se" ++ s
       else if "MBEDTLS_" `isPrefixOf` s
            then "SE" ++ s
            else "Cogent_" ++ s
mapName False (LCI.Ident s _ _) =
    if "mbedtls_" `isPrefixOf` s 
       then "se" ++ s
       else if "MBEDTLS_" `isPrefixOf` s
            then "sE" ++ s
            else "cogent_" ++ s

mapNameToUpper = mapName True
mapNameToLower = mapName False

mapInternal :: String -> LCI.Ident -> String
mapInternal fnam (LCI.Ident s _ _) = "local_" ++ (dropExtension $ fnam) ++ "_" ++ s

mapIfUpper :: LCI.Ident -> String
mapIfUpper idnam = if isUpper $ head s then mapNameToLower idnam else s
    where (Ident s _ _) = idnam

transTagName :: MonadTrav m => LCA.TypeName -> m CCS.TypeName
transTagName (LCA.TyComp (LCA.CompTypeRef (LCI.NamedRef idnam) kind _)) = 
    return $ kindPrefix kind ++ mapNameToUpper idnam
    where kindPrefix LCA.StructTag = "Struct_"
          kindPrefix LCA.UnionTag  = "Union_"
transTagName (LCA.TyComp (LCA.CompTypeRef ref@(LCI.AnonymousRef unam) kind _)) = do
    table <- LCA.getDefTable
    let (Just (Right tagdef)) = LCD.lookupTag ref table
    fnam <- srcFileName tagdef
    return $ kindPrefix kind ++ show (lineNr tagdef) ++ "_" ++ (map mapFileChar fnam)
    where kindPrefix LCA.StructTag = "Struct"
          kindPrefix LCA.UnionTag  = "Union"
transTagName (LCA.TyEnum (LCA.EnumTypeRef (LCI.NamedRef idnam) _)) = 
    return $ "Enum_" ++ mapNameToUpper idnam

transObjName :: MonadTrav m => LCI.Ident -> m CCS.VarName
transObjName idnam = do
    (Just decdef) <- LCA.lookupObject idnam
    fnam <- srcFileName decdef
    let lnk = LCA.declLinkage decdef
    return $ case decdef of
                  LCA.EnumeratorDef _ -> mapNameToLower idnam
                  _ -> mapObjectName idnam lnk fnam

mapObjectName :: LCI.Ident -> LCA.Linkage -> String -> String
mapObjectName idnam lnk fnam = 
    case lnk of
         LCA.InternalLinkage -> mapInternal fnam idnam
         LCA.ExternalLinkage -> mapNameToLower idnam
         LCA.NoLinkage -> mapIfUpper idnam

mapFileChar :: Char -> Char
mapFileChar '.' = '_'
mapFileChar '-' = '_'
mapFileChar c = c

fileName :: CNode a => a -> String
fileName = takeFileName . LCP.posFile . LCN.posOfNode . LCN.nodeInfo

lineNr :: CNode a => a -> Int
lineNr = LCP.posRow . LCN.posOfNode . LCN.nodeInfo

srcFileName :: (MonadTrav m, CNode a) => a -> m String
srcFileName n | "<stdin>" == fileName n = do
    (Just dummy) <- lookupObject stdinIdent
    return $ fileName dummy
srcFileName n = return $ fileName n

addInputName :: LCD.DefTable -> IO LCD.DefTable
addInputName table = do
    args <- getArgs
    fnam <- if null args 
               then error "Error: Source file name expected as argument" 
               else return $ head args
    return $ snd $ LCD.defineGlobalIdent stdinIdent (dummyDecl fnam) table

stdinIdent = (Ident "<stdin>" 0 undefNode)

dummyDecl :: String -> IdentDecl
dummyDecl fnam = Declaration $ Decl 
    (VarDecl NoName (DeclAttrs noFunctionAttrs NoStorage []) 
        (DirectType TyVoid noTypeQuals [])) 
        $ mkNodeInfoOnlyPos $ initPos fnam

