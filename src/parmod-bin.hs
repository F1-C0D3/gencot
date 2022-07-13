{-# LANGUAGE PackageImports #-}
module Main where

import System.Environment (getArgs)
import Text.JSON (encode)
import Text.Pretty.Simple (pStringNoColor)
import Data.Text.Lazy (unpack)
import Control.Monad (when,liftM)

import Language.C.Analysis
import Language.C.Data.Ident (identToString)
import Language.C.Analysis.DefTable (globalDefs)

import Gencot.Input (readFromInput_,getDeclEvents,getOwnDeclEvents)
import Gencot.Util.CallGraph (getCallGraph,runCTrav)
import Gencot.Util.Types (isExtern)
import Gencot.Items.Identifier (getTypedefNames)
import Gencot.Items.Types (getTypedefItemId)
import Gencot.Items.Properties (showProperties)
import Gencot.Json.Parmod (readParmodsFromFile,readParmodsFromInput)
import Gencot.Json.Translate (transGlobals)
import Gencot.Json.Process (showRemainingPars,getRequired,filterParmods,prefilterParmods,addParsFromInvokes,evaluateParmods,getFunName,mergeParmods,sortParmods,convertParmods)
import Gencot.Traversal (runWithTable)

main :: IO ()
main = do
    {- dispatch on component name -}
    args <- getArgs
    when (length args == 0) $ error "parmod component name expected"
    case head args of
        "gen" -> parmodGen $ tail args
        "proc" -> parmodProc $ tail args
        _ -> error $ "Unknown parmod component: " ++ head args

parmodGen :: [String] -> IO ()
parmodGen args = do
    {- test arguments -}
    when (length args < 2 || length args > 3) $ error "expected arguments: <original source file name> <used external items file> close?"
    {- parse and analyse C source and get global definitions -}
    table <- readFromInput_
    {- get input file name -}
    let fnam = head args
    {- get list of additional external items to process -}
    useditems <- (liftM ((filter (not . null)) . lines)) (readFile $ head $ tail args)
    {- Determine type names used directly in the Cogent compilation unit -}
    let unitTypeNames = getTypedefNames useditems
    {- test for close option -}
    let close = (length args) > 2
    {- convert symbol table to list of constructs to be processed -}
    let globals = if close
                    then getDeclEvents (globalDefs table) (declFilter unitTypeNames)
                    else getOwnDeclEvents (globalDefs table) defFilter
    {- get call graph -}
    cg <- getCallGraph table globals
    {- translate functions to Json parmod description -}
    parmods <- runCTrav cg table (fnam,(True,unitTypeNames)) $ transGlobals globals
    {- Output -}
    putStr $ unpack $ pStringNoColor $ encode parmods
    
defFilter :: DeclEvent -> Bool
defFilter (DeclEvent (FunctionDef _)) = True
defFilter (DeclEvent (ObjectDef _)) = True
defFilter (TagEvent (CompDef _)) = True
defFilter (TypeDefEvent _) = True
defFilter _ = False

declFilter :: [String] -> DeclEvent -> Bool
declFilter _ (DeclEvent (Declaration _)) = True
declFilter _ (TagEvent td) = isExtern td
declFilter tnams (TypeDefEvent td@(TypeDef idnam _ _ _)) = 
    isExtern td && elem (identToString idnam) tnams
declFilter _ _ = False

parmodProc :: [String] -> IO ()
parmodProc args = do
    {- test command line arguments -}
    when (length args == 0) $ error "parmod proc command expected"
    {- read JSON from standard input -}
    parmods <- readParmodsFromInput
    {- interprete first argument as command string -}
    case head args of
         "check" -> error "check not yet implemented"
         "funids" -> putStrLn $ unlines $ map getFunName parmods
         "unconfirmed" -> putStrLn $ unlines $ showRemainingPars parmods
         "required" -> putStrLn $ unlines $ getRequired parmods
         "sort" -> do
             when (length args == 1) $ error "sort: filename expected"
             funids <- readFile $ head $ tail args
             outputJson $ sortParmods parmods $ lines funids
         "filter" -> do
             when (length args == 1) $ error "filter: filename expected"
             funids <- readFile $ head $ tail args
             outputJson $ filterParmods parmods $ lines funids
         "prefilter" -> do
             when (length args == 1) $ error "prefilter: filename expected"
             funids <- (liftM ((filter (not . null)) . lines)) $ readFile $ head $ tail args
             outputJson $ prefilterParmods parmods funids
         "merge" -> do
             when (length args == 1) $ error "merge: filename expected"
             parmods2 <- readParmodsFromFile $ head $ tail args
             outputJson $ addParsFromInvokes $ mergeParmods parmods parmods2
         "eval" -> outputJson $ evaluateParmods parmods
         "out" -> putStrLn $ showProperties $ convertParmods parmods
         _ -> error $ "Unknown command: " ++ head args

outputJson parmods = putStr $ unpack $ pStringNoColor $ encode parmods
