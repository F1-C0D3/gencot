{-# LANGUAGE PackageImports #-}
module Main where

import System.Environment (getArgs)
import Control.Monad (when,liftM)
import Text.JSON (encode)
import Text.Pretty.Simple (pStringNoColor)
import Data.Text.Lazy (unpack)

import Gencot.Json.Process (showRemainingPars,getRequired,filterParmods,prefilterParmods,addParsFromInvokes,evaluateParmods,getFunName,mergeParmods,sortParmods,parmodsToProps,parmodsToOmitProps)
import Gencot.Json.Parmod (readParmodsFromFile,readParmodsFromInput)
import Gencot.Items.Properties (showProperties)

main :: IO ()
main = do
    {- get command line arguments -}
    args <- getArgs
    when (length args == 0) $ error "Command expected"
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
         "out" -> putStrLn $ showProperties $ parmodsToProps parmods
         "omit" -> putStrLn $ showProperties $ parmodsToOmitProps parmods
         _ -> error $ "Unknown command: " ++ head args

outputJson parmods = putStr $ unpack $ pStringNoColor $ encode parmods


