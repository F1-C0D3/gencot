{-# LANGUAGE PackageImports #-}
module Main where

import System.Environment (getArgs)
import Control.Monad (when)
import Text.JSON (encode)
import Text.Pretty.Simple (pStringNoColor)
import Data.Text.Lazy (unpack)

import Gencot.Json.Process (readParmods,showRemainingPars,showRequired,addRequired,addParsFromInvokes)

main :: IO ()
main = do
    {- get JSON file name -}
    args <- getArgs
    when (null args ) $ error "Error: JSON file name expected as first argument" 
    {- read JSON from first input file -}
    parmods <- readParmods $ head args
    if (length args) == 1
       then do -- show
           let rp = showRemainingPars parmods
           putStrLn $ (show $ length rp) ++ " remaining parameters to be processed:"
           putStrLn $ unlines rp
           let rq = showRequired parmods
           putStrLn $ (show $ length rq) ++ " additional required dependencies:"
           putStrLn $ unlines rq
       else do -- addto
           {- read JSON from second input file -}
           pmsrc <- readParmods $ head $ tail args
           let pmres = addParsFromInvokes $ addRequired parmods pmsrc
           {- Output -}
           putStr $ unpack $ pStringNoColor $ encode pmres

       


