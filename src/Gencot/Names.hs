{-# LANGUAGE PackageImports #-}
module Gencot.Names where

import Data.Char (isUpper,toUpper,toLower)
import Data.List (isPrefixOf,intercalate,lines,words,break,find)
import System.FilePath (takeFileName, dropExtension)

import Language.C.Data.Ident as LCI
import Language.C.Data.Node as LCN
import Language.C.Data.Position as LCP
import Language.C.Syntax.AST as LCS
import Language.C.Analysis as LCA
import Language.C.Analysis.DefTable as LCD

class (Monad m) => FileNameTrav m where
    getFileName :: m String

type NamePrefixReplacement = (String, (String, String))
type NamePrefixMap = [NamePrefixReplacement]

class (FileNameTrav m) => MapNamesTrav m where
    matchPrefix :: String -> m NamePrefixReplacement

-- | Read a name prefix map from a file.
readNameMapFromFile :: FilePath -> IO NamePrefixMap
readNameMapFromFile file = do 
    inp <- readFile file 
    return $ parseNameMap inp

-- | Parse the string representation of a name prefix map 
-- It consists of a sequence of lines where each line specifies replacements for a prefix.
-- Empty lines must be ignored. 
parseNameMap :: String -> NamePrefixMap
parseNameMap inp = map parseNameMapLine $ ((filter (not . null)) . lines) inp

-- | Parse a single line of a name prefix map.
-- If the line contains a single word it specifies a replacement for the empty prefix.
-- Otherwise the first word is the prefix, the second word is the replacement, and all other words are ignored.
parseNameMapLine :: String -> NamePrefixReplacement
parseNameMapLine line = 
    if length ws == 1 
       then ("", readReplacements $ head ws)
       else (head ws, readReplacements $ head $ tail ws)
    where ws = words line

-- A replacement has the form upper|lower[|...] (where the second bar and everything after it are ignored)
-- or repl (which is converted to upper and lower by converting its first character).
readReplacements :: String -> (String,String)
readReplacements repl =
    if null lower
       then ((toUpper $ head upper) : (tail upper), (toLower $ head upper) : (tail upper))
       else (upper, lower)
    where (upper,rest) = break (== '|') repl
          (lower,_) = if null rest then ("","") else break (== '|') $ tail rest

lookupPrefix :: String -> NamePrefixMap -> NamePrefixReplacement
lookupPrefix name npm =
    case find (\(pre,_) -> pre `isPrefixOf` name) npm of
         Nothing -> ("", ("Cogent_","cogent_"))
         Just repl -> repl

mapName :: MapNamesTrav f => Bool -> LCI.Ident -> f String
mapName True (LCI.Ident s _ _) = do
    (pre,(repl,_)) <- matchPrefix s
    return (repl ++ (drop (length pre) s))
mapName False (LCI.Ident s _ _) = do
    (pre,(_,repl)) <- matchPrefix s
    return (repl ++ (drop (length pre) s))

mapNameToUpper :: MapNamesTrav f => LCI.Ident -> f String
mapNameToUpper = mapName True

mapNameToLower :: MapNamesTrav f => LCI.Ident -> f String
mapNameToLower = mapName False

mapInternal :: String -> LCI.Ident -> String
mapInternal fnam (LCI.Ident s _ _) = "local_" ++ (dropExtension $ fnam) ++ "_" ++ s

mapIfUpper ::MapNamesTrav f => LCI.Ident -> f String
mapIfUpper idnam =
    if (isUpper $ head s) || "_" `isPrefixOf` s then mapNameToLower idnam else return s
    where (Ident s _ _) = idnam

transTagName :: (MapNamesTrav f, MonadTrav f) => LCA.TypeName -> f String
transTagName (LCA.TyComp (LCA.CompTypeRef (LCI.NamedRef idnam) kind _)) = do
    upper <- mapNameToUpper idnam
    return $ kindPrefix kind ++ "_" ++ upper
transTagName (LCA.TyComp (LCA.CompTypeRef ref@(LCI.AnonymousRef unam) knd _)) = do
    table <- LCA.getDefTable
    let (Just (Right (LCA.CompDef (LCA.CompType _ _ _ _ n)))) = LCD.lookupTag ref table
    sfn <- getFileName
    return $ (kindPrefix knd ++ anonCompTypeName sfn n)
transTagName (LCA.TyEnum (LCA.EnumTypeRef (LCI.NamedRef idnam) _)) = do
    upper <- mapNameToUpper idnam
    return $ "Enum_" ++ upper

anonCompTypeName :: CNode a => String -> a -> String
anonCompTypeName sfn n = 
    show (lineNr n) ++ "_" ++ (map mapFileChar $ srcFileName sfn n)

kindPrefix LCA.StructTag = "Struct"
kindPrefix LCA.UnionTag  = "Union"

transObjName :: (MapNamesTrav f, MonadTrav f) => LCI.Ident -> f String
transObjName idnam = do
    mdecdef <- LCA.lookupObject idnam
    let (Just decdef) = mdecdef
    fnam <- getFileName 
    let lnk = LCA.declLinkage decdef
    case decdef of
         LCA.EnumeratorDef _ -> mapNameToLower idnam
         _ -> mapObjectName idnam lnk fnam decdef

mapObjectName :: (CNode a, MapNamesTrav f) => LCI.Ident -> LCA.Linkage -> String -> a -> f String
mapObjectName idnam lnk fnam n = 
    case lnk of
         LCA.InternalLinkage -> return $ mapInternal (srcFileName fnam n) idnam
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

-- | Convert an array type name CArr<size> to the component name arr<size>
arrDerivCompNam :: String -> String
arrDerivCompNam ('C' : 'A' : rest) = 'a' : rest

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

globStateType :: String -> String
globStateType gs = ("GlobState" ++ (drop 2 gs))

fileName :: CNode a => a -> String
fileName n =
    case LCN.fileOfNode n of
         Nothing -> "<unknown>"
         Just res -> takeFileName res

lineNr :: CNode a => a -> Int
lineNr = LCP.posRow . LCN.posOfNode . LCN.nodeInfo

srcFileName :: CNode a => String -> a -> String
srcFileName sfn n | "<stdin>" == fileName n = sfn
srcFileName _ n = fileName n
