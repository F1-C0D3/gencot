module Main where

import System.Environment (getArgs)
import Control.Monad (when)

import Gencot.Items.Properties (readPropertiesFromInput, readPropertiesFromFile, showProperties, combineProperties, getToplevelItemIds, filterItemsPrefixes)

main :: IO ()
main = do
    {- get command line arguments -}
    args <- getArgs
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
             when (length args == 1) $ error "merge: filename expected"
             items <- readFile $ head $ tail args
             putStrLn $ showProperties $ filterItemsPrefixes (lines items) ipm
         _ -> error $ "Unknown command: " ++ head args
 
