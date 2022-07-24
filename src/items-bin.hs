{-# LANGUAGE PackageImports #-}
module Main where

import System.Environment (getArgs)
import Control.Monad (liftM,when)
import Data.List (nub)
import Data.Map (empty)

import Language.C.Analysis
import Language.C.Data.Ident (identToString)
import Language.C.Analysis.DefTable (globalDefs)

import Gencot.Input (readFromInput_,getOwnDeclEvents,getDeclEvents)
import Gencot.Package (readPackageFromInput_,readPackageFromInput,getIdentInvocations,getOwnCallGraphs,foldTables,foldTypeCarrierSets)
import Gencot.Util.Types (collectTypeCarriers,transCloseUsedCarriers,carriesNamedType,usedTypeNames,externTypeNames,isExtern)
import Gencot.Items.Identifier (getTypedefNames)
import Gencot.Items.Types (getItemAssocType,getToplevelItemId,getTypedefItemId,getTagItemId,getEnumItemId)
import Gencot.Items.Properties (readPropertiesFromInput, readPropertiesFromFile, showProperties, combineProperties, getToplevelItemIds, filterItemsPrefixes)
import Gencot.Items.Translate (transGlobals,functionsInGlobals)
import Gencot.Traversal (runFTrav,runWithTable)

main :: IO ()
main = do
    {- dispatch on component name -}
    args <- getArgs
    when (length args == 0) $ error "items component name expected"
    case head args of
        "externs" -> itemsExterns $ tail args
        "extfuns" -> itemsExtfuns $ tail args
        "gen" -> itemsGen $ tail args
        "proc" -> itemsProc $ tail args
        "used" -> itemsUsed $ tail args
        _ -> error $ "Unknown items component: " ++ head args

itemsExterns :: [String] -> IO ()
itemsExterns args = do
    {- test arguments -}
    when (null args || length args > 1) $ error "expected arguments: <used external items file name>"
    {- get list of additional external items to process -}
    useditems <- (liftM ((filter (not . null)) . lines)) (readFile $ head args)
    {- parse and analyse C sources and get global definitions -}
    tables <- readPackageFromInput_
    {- combine symbol tables -}
    table <- foldTables tables
    {- Get declarations of used external functions and objects -}
    let usedExtToplvl = getDeclEvents (globalDefs table) (usedFilter useditems)
    {- Determine type names used directly in the Cogent compilation unit -}
    let unitTypeNames = getTypedefNames useditems
    {- determine default properties for all used items in globals -}
    ipm <- runFTrav table ("",[],empty,(True,unitTypeNames)) $ transGlobals usedExtToplvl
    {- Output -}
    putStrLn $ showProperties ipm

usedFilter :: [String] -> DeclEvent -> Bool
usedFilter usedItems tc = elem (getToplevelItemId tc) usedItems

itemsExtfuns :: [String] -> IO ()
itemsExtfuns args = do
    {- test arguments -}
    when (null args || length args > 1) $ error "expected arguments: <used external items file name>"
    {- get list of additional external items to process -}
    useditems <- (liftM ((filter (not . null)) . lines)) (readFile $ head args)
    {- parse and analyse C sources and get global definitions -}
    tables <- readPackageFromInput_
    {- combine symbol tables -}
    table <- foldTables tables
    {- Get declarations of used external functions and objects -}
    let usedExtDecls = getDeclEvents (globalDefs table) (usedDeclFilter useditems)
    {- Determine type names used directly in the Cogent compilation unit -}
    let unitTypeNames = getTypedefNames useditems
    {- determine item ids of used external functions -}
    iids <- runFTrav table ("",[],empty,(True,unitTypeNames)) $ functionsInGlobals $ getDeclEvents (globalDefs table) (usedFilter useditems)
    {- Output -}
    putStrLn $ unlines iids

usedDeclFilter :: [String] -> DeclEvent -> Bool
usedDeclFilter usedItems e@(DeclEvent (Declaration _)) = elem (getToplevelItemId e) usedItems
usedDeclFilter _ _ = False

itemsGen :: [String] -> IO ()
itemsGen args = do
    {- test arguments -}
    when (null args || length args > 1) $ error "expected arguments: <original source file name>"
    {- parse and analyse C source and get global definitions -}
    table <- readFromInput_
    {- get input file name -}
    let fnam = head args
    {- determine default properties for all items in globals -}
    ipm <- runFTrav table (fnam,[],empty,(False,[])) $ transGlobals $ getOwnDeclEvents (globalDefs table) defFilter
    {- Output -}
    putStrLn $ showProperties ipm

    
defFilter :: DeclEvent -> Bool
defFilter (DeclEvent (FunctionDef _)) = True
defFilter (DeclEvent (ObjectDef _)) = True
defFilter (TagEvent (CompDef _)) = True
defFilter (TypeDefEvent _) = True
defFilter _ = False

itemsProc :: [String] -> IO ()
itemsProc args = do
    {- test command line arguments -}
    when (length args == 0) $ error "Command expected"
    {- read property declarations from standard input -}
    ipm <- readPropertiesFromInput
    {- interprete first argument as command string -}
    case head args of
         "merge" -> do
             when (length args == 1) $ error "merge: filename expected"
             ipm2 <- readPropertiesFromFile $ head $ tail args
             putStrLn $ showProperties $ combineProperties ipm ipm2
         "idlist" -> 
             putStrLn $ unlines $ getToplevelItemIds ipm
         "filter" -> do
             when (length args == 1) $ error "filter: filename expected"
             items <- (liftM ((filter (not . null)) . lines)) (readFile $ head $ tail args)
             putStrLn $ showProperties $ filterItemsPrefixes items ipm
         _ -> error $ "Unknown command: " ++ head args

itemsUsed :: [String] -> IO ()
itemsUsed args = do
    {- test arguments -}
    when (null args || length args > 1) $ error "expected arguments: <additional items file name>"
    {- get list of additional external items to process -}
    additems <- (liftM ((filter (not . null)) . lines)) (readFile $ head args)
    {- parse and analyse C sources and get global definitions and used types -}
    (tables,initialTypeCarrierSets) <- (liftM unzip) $ readPackageFromInput [] (collectTypeCarriers carriesNamedType)
    {- Determine all call graphs -}
    cgs <- getOwnCallGraphs tables
    {- Retrieve all invocations of named functions -}
    invks <- getIdentInvocations cgs
    {- combine symbol tables -}
    table <- foldTables tables
    {- combine sets of initial type carriers -}
    let initialTypeCarriers = foldTypeCarrierSets initialTypeCarrierSets table
    {- Get declarations of external functions and objects which are invoked or additionally specified -}
    let extDecls = getDeclEvents (globalDefs table) (extDeclFilter invks additems)
    {- Get definitions of additionally specified external tags and type names -}
    let extTypes = getDeclEvents (globalDefs table) (extTypeFilter additems)
    {- build directly used type carriers by adding initial and filtered external -}
    let unitTypeCarriers = initialTypeCarriers ++ filter carriesNamedType extDecls
    {- Determine type names used directly in the Cogent compilation unit or additionally specified-}
    let unitTypeNames = (usedTypeNames unitTypeCarriers) ++ (externTypeNames extTypes)
    {- construct transitive closure of used type carriers -}
    let typeCarriers = transCloseUsedCarriers table (unitTypeCarriers ++ extTypes)
    {- construct item associated types for external functions/objects and used named type carriers -}
    iats <- runWithTable table $ mapM getItemAssocType $ nub ((filter (isExternNamedDef unitTypeNames) typeCarriers) ++ extDecls)
    {- Output -}
    putStrLn $ unlines $ map fst iats

isExternNamedDef :: [String] -> DeclEvent -> Bool
isExternNamedDef _ (TagEvent cd) = isExtern cd
isExternNamedDef utn (TypeDefEvent td) = isExtern td && (elem (identToString $ identOfTypeDef td) utn)
isExternNamedDef _ _ = False

extDeclFilter :: [IdentDecl] -> [String] -> DeclEvent -> Bool
extDeclFilter invks iids e@(DeclEvent decl@(Declaration _)) = invokedOrListed decl
    where invokedOrListed decl = elem decl invks || elem (getToplevelItemId e) iids
extDeclFilter _ _ _ = False

extTypeFilter :: [String] -> DeclEvent -> Bool
extTypeFilter iids (TagEvent td@(CompDef ct)) = 
    isExtern td && elem (getTagItemId ct "") iids
extTypeFilter iids (TagEvent td@(EnumDef (EnumType sueref _ _ _))) = 
    isExtern td && elem (getEnumItemId sueref) iids
extTypeFilter iids (TypeDefEvent td@(TypeDef idnam _ _ _)) = 
    isExtern td && elem (getTypedefItemId idnam) iids
extTypeFilter _ _ = False

