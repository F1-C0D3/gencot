{-# LANGUAGE PackageImports #-}
module Main where

import System.Environment (getArgs)
import Control.Monad (when,liftM)
import Data.Map (empty)
import qualified Data.Set as Set (unions)

import Language.C.Data.Ident
import Language.C.Analysis
import Language.C.Analysis.DefTable (globalDefs)

import Gencot.Input (readFromInput_,getOwnDeclEvents,getDeclEvents)
import Gencot.Items.Properties (readPropertiesFromFile)
import Gencot.Items.Identifier (getTypedefNames)
import Gencot.Items.Types (getItemAssocType,getEnumItemId,getTagItemId,getTypedefItemId)
import Gencot.Names (readNameMapFromFile)
import Gencot.Traversal (runFTrav)
import Gencot.Cogent.Output (prettyTopLevels,prettyGenTopLevels)
import Gencot.Cogent.Translate (transGlobals,genTypeDefs)
import Gencot.C.Output (showTopLevels)
import Gencot.C.Generate (genEntries)
import Gencot.Text.Decls (transDecls)
import Gencot.Text.CallGraph (callGraphToIdentRel,prepareCallGraphMap,printCallGraphMap)
import Gencot.Text.DumpCAst (dumpGlobals)
import Gencot.Package (readPackageFromInput_,readPackageFromInput,foldTables,foldTypeCarrierSets,getOwnCallGraphs)
import Gencot.Util.Types (resolveTypedef,collectTypeCarriers,carriesNonPrimitive,isExtern)

main :: IO ()
main = do
    {- dispatch on component name -}
    args <- getArgs
    when (length args == 0) $ error "gencot component name expected"
    case head args of
        "check" -> gencotCheck $ tail args
        "translate" -> gencotTranslate $ tail args
        "entries" -> gencotEntries $ tail args
        "deccomments" -> gencotDeccomments $ tail args
        "externs" -> gencotExterns $ tail args
        "exttypes" -> gencotExttypes $ tail args
        "dvdtypes" -> gencotDvdtypes $ tail args
        "callgraph" -> gencotCallgraph $ tail args
        "dumpc" -> gencotDumpc $ tail args
        _ -> error $ "Unknown gencot component: " ++ head args


gencotCheck :: [String] -> IO ()
gencotCheck args = do
    _ <- readFromInput_
    return ()

gencotTranslate :: [String] -> IO ()
gencotTranslate args = do
    {- test arguments -}
    when (length args /= 5) 
        $ error "expected arguments: <original source file name> <name prefix map> <item properties file name> <used external items file name> <translation configuration string>"
    {- get own file name -}
    let fnam = head args
    {- get name prefix map -}
    npm <- readNameMapFromFile $ head $ tail args
    {- get item property map -}
    ipm <- readPropertiesFromFile $ head $ tail $ tail args
    {- get list of used external items -}
    useditems <- (liftM ((filter (not . null)) . lines)) $ readFile $ head $ tail $ tail $ tail args
    {- get translation configuration string -}
    let tconf = head $ tail $ tail $ tail $ tail args
    {- parse and analyse C source and get global definitions -}
    table <- readFromInput_
    {- Determine type names used directly in the Cogent compilation unit -}
    let unitTypeNames = getTypedefNames useditems
    {- translate global declarations and definitions to Cogent -}
    toplvs <- runFTrav table (fnam,npm, ipm,(True,unitTypeNames),tconf) $ transGlobals $ getOwnDeclEvents (globalDefs table) translateFilter
    {- Output -}
    if elem 'G' tconf
       then print $ prettyGenTopLevels toplvs
       else print $ prettyTopLevels toplvs

translateFilter :: DeclEvent -> Bool
translateFilter (TagEvent (EnumDef (EnumType (AnonymousRef _) _ _ _))) = False
translateFilter (DeclEvent (Declaration _)) = False
translateFilter _ = True

gencotEntries :: [String] -> IO ()
gencotEntries args = do
    {- test arguments -}
    when (length args /= 4) 
        $ error "expected arguments: <original source file name> <name prefix map> <item properties file name> <used external items file name>"
    {- get own file name -}
    let fnam = head args
    {- get name prefix map -}
    npm <- readNameMapFromFile $ head $ tail args
    {- get item property map -}
    ipm <- readPropertiesFromFile $ head $ tail $ tail args
    {- get list of used external items -}
    useditems <- (liftM ((filter (not . null)) . lines)) $ readFile $ head $ tail $ tail $ tail args
    {- parse and analyse C source and get global definitions -}
    table <- readFromInput_
    {- Determine type names used directly in the Cogent compilation unit -}
    let unitTypeNames = getTypedefNames useditems
    {- translate global declarations and definitions to Cogent -}
    wrappers <- runFTrav table (fnam,npm,ipm,(True,unitTypeNames),"") $ genEntries $ getOwnDeclEvents (globalDefs table) entriesFilter
    {- Output -}
    putStrLn $ showTopLevels wrappers

entriesFilter :: DeclEvent -> Bool
entriesFilter (DeclEvent fdef@(FunctionDef _)) | declLinkage fdef == ExternalLinkage = True
entriesFilter (DeclEvent (ObjectDef _)) = True
entriesFilter _ = False

gencotDeccomments :: [String] -> IO ()
gencotDeccomments args = do
    {- test arguments -}
    when (length args /= 1) 
        $ error "expected arguments: <name prefix map>"
    {- get name prefix map -}
    npm <- readNameMapFromFile $ head args
    table <- readFromInput_
    out <- runFTrav table ("", npm, empty,(False,[]),"") $ transDecls $ getOwnDeclEvents (globalDefs table) declFilter
    putStrLn $ unlines out

declFilter :: DeclEvent -> Bool
declFilter (DeclEvent (Declaration (Decl (VarDecl _ (DeclAttrs _ (FunLinkage ExternalLinkage) _) _) _))) = True
declFilter (DeclEvent (Declaration (Decl (VarDecl _ (DeclAttrs _ (Static ExternalLinkage _) _) _) _))) = True
declFilter _ = False

gencotExterns :: [String] -> IO ()
gencotExterns args = do
    {- test arguments -}
    when (length args /= 3) 
        $ error "expected arguments: <name prefix map> <item properties file name> <external items file name>"
    {- get name prefix map -}
    npm <- readNameMapFromFile $ head args
    {- get item property map -}
    ipm <- readPropertiesFromFile $ head $ tail args
    {- get list of used external items -}
    useditems <- (liftM ((filter (not . null)) . lines)) $ readFile $ head $ tail $ tail args
    {- parse and analyse C sources and get global definitions -}
    tables <- readPackageFromInput_
    {- combine symbol tables -}
    table <- foldTables tables
    {- Get declarations of functions and objects listed in useditems -}    
    let extDecls = getDeclEvents (globalDefs table) (externsFilter useditems)
    {- Determine type names used directly in the Cogent compilation unit -}
    let unitTypeNames = getTypedefNames useditems
    {- translate external function declarations to Cogent abstract function definitions -}
    absdefs <- runFTrav table ("",npm,ipm,(True,unitTypeNames),"") $ transGlobals extDecls
    {- Output -}
    print $ prettyTopLevels absdefs

-- | Predicate for all functions completely declared and all declared objects 
-- which are listed in iids.
-- Since for functions and objects with external linkage the item identifiers are the C names, 
-- we can directly match the C names to the identifiers in iids.
externsFilter :: [String] -> DeclEvent -> Bool
externsFilter iids (DeclEvent decl@(Declaration _)) = 
    case resolveTypedef $ declType decl of
         FunctionType (FunType _ _ _) _ -> listed decl
         FunctionType _ _ -> False
         _ -> listed decl
    where listed decl = elem (identToString $ declIdent decl) iids
externsFilter _ _ = False

gencotExttypes :: [String] -> IO ()
gencotExttypes args = do
    {- test arguments -}
    when (length args /= 3) 
        $ error "expected arguments: <name prefix map> <items properties file name> <external items file name>"
    {- get name prefix map -}
    npm <- readNameMapFromFile $ head args
    {- get item property map -}
    ipm <- readPropertiesFromFile $ head $ tail args
    {- get list of used external items -}
    useditems <- (liftM ((filter (not . null)) . lines)) $ readFile $ head $ tail $ tail args
    {- parse and analyse C sources and get global definitions -}
    tables <- readPackageFromInput_
    {- combine symbol tables -}
    table <- foldTables tables
    {- Get declarations of listed tag and type definitions -}    
    let typeDefs = getDeclEvents (globalDefs table) (exttypesFilter useditems)
    {- translate type definitions in system include files -}
    toplvs <- runFTrav table ("",npm,ipm,(True,getTypedefNames useditems),"") $ transGlobals typeDefs
    {- Output -}
    print $ prettyTopLevels toplvs

exttypesFilter :: [String] -> DeclEvent -> Bool
exttypesFilter iids (TagEvent cd@(CompDef ct)) = elem (getTagItemId ct "") iids
exttypesFilter iids (TagEvent cd@(EnumDef (EnumType sueref _ _ _))) = elem (getEnumItemId sueref) iids
exttypesFilter iids (TypeDefEvent (TypeDef idnam _ _ _)) = elem (getTypedefItemId idnam) iids
exttypesFilter _ _ = False

gencotDvdtypes :: [String] -> IO ()
gencotDvdtypes args = do
    {- test arguments -}
    when (length args /= 3) 
        $ error "expected arguments: <name prefix map> <item property file name> <external items file name>"
    {- get name prefix map -}
    npm <- readNameMapFromFile $ head args
    {- get item property map -}
    ipm <- readPropertiesFromFile $ head $ tail args
    {- get list of used external items -}
    useditems <- (liftM ((filter (not . null)) . lines)) $ readFile $ head $ tail $ tail args
    {- parse and analyse C sources and get global definitions and used types -}
    (tables,initialTypeCarrierSets) <- (liftM unzip) $ readPackageFromInput [] (collectTypeCarriers carriesNonPrimitive)
    {- combine symbol tables -}
    table <- foldTables tables
    {- combine sets of initial type carriers -}
    let initialTypeCarriers = foldTypeCarrierSets initialTypeCarrierSets table
    {- Get declarations of used external functions and objects -}    
    let extDecls = getDeclEvents (globalDefs table) (dvdtypesFilter useditems)
    {- build type carriers in the Cogent compilation unit by adding initial and external -}
    let unitTypeCarriers = initialTypeCarriers ++ extDecls
    {- Determine external type names used directly in the Cogent compilation unit -}
    let unitTypeNames = getTypedefNames useditems
    {- generate abstract definitions for derived types in all type carriers -}
    toplvs <- runFTrav table ("", npm, ipm,(True,unitTypeNames),"") $ genTypeDefs unitTypeCarriers
    {- Output -}
    print $ prettyTopLevels toplvs

dvdtypesFilter :: [String] -> DeclEvent -> Bool
dvdtypesFilter iids (DeclEvent decl@(Declaration _)) = 
    elem (identToString $ declIdent decl) iids
dvdtypesFilter iids (TagEvent td@(CompDef ct)) = 
    isExtern td && elem (getTagItemId ct "") iids
dvdtypesFilter iids (TypeDefEvent td@(TypeDef idnam _ _ _)) = 
    isExtern td && elem (getTypedefItemId idnam) iids
dvdtypesFilter _ _ = False

gencotCallgraph :: [String] -> IO ()
gencotCallgraph args = do
    {- get list of original input file names -}
    fnams <- (liftM ((filter (not . null)) . lines)) (if null args then return "" else readFile $ head args)
    {- parse and analyse C sources and get global definitions -}
    tables <- readPackageFromInput_
    {- Determine all call graphs -}
    cgs <- getOwnCallGraphs tables
    {- Translate call graphs to relation on function ids -}
    let idRel = Set.unions $ map (uncurry callGraphToIdentRel) $ zip cgs fnams
    {- Translate relation to map to pre- and postdomain-}
    let idmap = prepareCallGraphMap idRel
    {- Output -}
    putStrLn $ unlines $ printCallGraphMap idmap

gencotDumpc :: [String] -> IO ()
gencotDumpc args = do
    {- parse and analyse C source and get global definitions -}
    table <- readFromInput_
    {- dump global declarations and definitions -}
    let lines = dumpGlobals $ getOwnDeclEvents (globalDefs table) dumpcFilter
    {- Output -}
    putStrLn $ unlines lines

dumpcFilter :: DeclEvent -> Bool
dumpcFilter _ = True
