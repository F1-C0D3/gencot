{-# LANGUAGE PackageImports #-}
module Gencot.Names where

import Data.Char (isUpper)
import Data.List (isPrefixOf)
import System.FilePath (takeFileName, dropExtension)

import Language.C.Data.Ident as LCI
import Language.C.Data.Node as LCN
import Language.C.Data.Position as LCP
import Language.C.Syntax.AST as LCS
import Language.C.Analysis as LCA
import Language.C.Analysis.DefTable as LCD

class (Monad m) => FileNameTrav m where
    getFileName :: m String

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
            then "se" ++ s
            else "cogent_" ++ s

mapNameToUpper = mapName True
mapNameToLower = mapName False

mapInternal :: String -> LCI.Ident -> String
mapInternal fnam (LCI.Ident s _ _) = "local_" ++ (dropExtension $ fnam) ++ "_" ++ s

mapIfUpper :: LCI.Ident -> String
mapIfUpper idnam = if (isUpper $ head s) || "_" `isPrefixOf` s then mapNameToLower idnam else s
    where (Ident s _ _) = idnam

transTagName :: (FileNameTrav f, MonadTrav f) => LCA.TypeName -> f String
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

transObjName :: (FileNameTrav f, MonadTrav f) => LCI.Ident -> f String
transObjName idnam = do
    mdecdef <- LCA.lookupObject idnam
    let (Just decdef) = mdecdef
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

mapPtrDeriv :: String
mapPtrDeriv = "P"

mapArrDeriv :: LCA.ArraySize -> String
mapArrDeriv (LCA.ArraySize _ (LCS.CConst (LCS.CIntConst i _))) = "A" ++ show i
mapArrDeriv (LCA.ArraySize _ (LCS.CVar (LCI.Ident s _ _) _)) = 
    let sep = findSepCharFor s
    in "A" ++ [sep] ++ s ++ [sep] 
mapArrDeriv _ = "AXX"

mapFunDeriv :: LCA.FunType -> [(Bool,String,String)] -> String
mapFunDeriv (LCA.FunTypeIncomplete _) _ = "F_UnknownCogentParameters_"
mapFunDeriv (LCA.FunType _ _ _) ps = 
    let sep = findSepCharFor $ concat $ map (\(_,x,y) -> x ++ y) ps
    in "F_" ++ (concat $ map (mkParTypeName sep) ps) ++ (if null ps then "" else [sep]) ++ "_"

mapParmodDeriv :: String -> String
mapParmodDeriv "yes" = "L"
mapParmodDeriv "readonly" = "R"
mapParmodDeriv "no" = "R"
mapParmodDeriv _ = ""

findSepCharFor :: String -> Char
findSepCharFor s = 
    findSepCharIn "XYZxyzABCDEFGHIJKMNOPQSTVWabcdefghijklmnopqrstuvw"
    -- omit L and R which are used for mapParmodDeriv and U which is used for mkParTypeName
    where findSepCharIn (c : r) = if elem c s then findSepCharIn r else c
          findSepCharIn [] = error ("No separation char found for: " ++ s)

mkNonLin :: String -> String
mkNonLin d = 'U' : d

mkDerivedName :: String -> String -> String
mkDerivedName deriv base = deriv ++ sep ++ base
    where sep = if null deriv || last deriv == '_' then "" else "_"

mkParTypeName :: Char -> (Bool,String,String) -> String
mkParTypeName sep (ubx,deriv,base) = 
    [sep] ++ (mkDerivedName (if ubx then "U"++deriv else deriv) base)

mapFileChar :: Char -> Char
mapFileChar '.' = '_'
mapFileChar '-' = '_'
mapFileChar c = c

fileName :: CNode a => a -> String
fileName n = -- takeFileName . LCP.posFile . LCN.posOfNode . LCN.nodeInfo
    case LCN.fileOfNode n of
         Nothing -> "<unknown>"
         Just res -> takeFileName res

lineNr :: CNode a => a -> Int
lineNr = LCP.posRow . LCN.posOfNode . LCN.nodeInfo

srcFileName :: (FileNameTrav f, CNode a) => a -> f String
srcFileName n | "<stdin>" == fileName n = getFileName
srcFileName n = return $ fileName n

