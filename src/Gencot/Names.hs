{-# LANGUAGE PackageImports #-}
module Gencot.Names where

import Data.Char (isUpper)
import Data.List (isPrefixOf,intercalate)
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
mapPtrDeriv = "CPtr"

mapPtrVoid :: String
mapPtrVoid = "CVoidPtr"

mapArrDeriv :: LCA.ArraySize -> String
mapArrDeriv (LCA.ArraySize _ (LCS.CConst (LCS.CIntConst i _))) = "CArr" ++ show i
mapArrDeriv (LCA.ArraySize _ (LCS.CVar (LCI.Ident s _ _) _)) = 
    let sep = findSepCharFor s
    in "CArr" ++ [sep] ++ s ++ [sep] 
mapArrDeriv _ = "CArrXX"

arrDerivHasSize :: String -> Bool
arrDerivHasSize nam = nam /= "CArrXX"

arrDerivToUbox :: String -> String
arrDerivToUbox ('C' : rest) = "U" ++ rest

mapFunDeriv :: Bool -> String
mapFunDeriv False = "CFunInc"
mapFunDeriv True = "CFunPtr"

mapMayNull :: String
mapMayNull = "MayNull"

mapUboxStep = "U_"
rmUboxStep ('U' : '_' : rest) = rest
rmUboxStep nam = nam

mapModStep = "M_"
mapRoStep = "R_"

mapPtrStep = "P_"

mapMayNullStep = "N_"

rmMayNullStepThroughRo ('R' : '_' : 'N' : '_' : rest) = mapRoStep ++ rest
rmMayNullStepThroughRo ('N' : '_' : rest) = rest
rmMayNullStepThroughRo nam = nam

addMayNullStep ('R' : '_' : rest) = mapRoStep ++ (addMayNullStep rest)
addMayNullStep s@('N' : '_' : rest) = s
addMayNullStep s = mapMayNullStep ++ s

mapArrStep :: LCA.ArraySize -> String
mapArrStep (LCA.ArraySize _ (LCS.CConst (LCS.CIntConst i _))) = "A" ++ (show i) ++ "_"
mapArrStep (LCA.ArraySize _ (LCS.CVar (LCI.Ident s _ _) _)) = 
    ['A',sep] ++ s ++ [sep,'_'] 
    where sep = findSepCharFor s
mapArrStep _ = "AXX_"

mapIncFunStep = "F_"
mapNamFunStep = "FNN_"

mapFunStep :: [String] -> String
mapFunStep ps =
    "F" ++ [sep] ++ (intercalate [sep] ps) ++ [sep,'_'] 
    where sep = findSepCharFor $ concat ps

findSepCharFor :: String -> Char
findSepCharFor s = 
    findSepCharIn "XYZxyzABCDEFGHIJKLMNOPQRSTUVWabcdefghijklmnopqrstuvw"
    where findSepCharIn (c : r) = if elem c s then findSepCharIn r else c
          findSepCharIn [] = error ("No separation char found for: " ++ s)

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

