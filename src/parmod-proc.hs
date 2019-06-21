{-# LANGUAGE PackageImports #-}
module Main where

import System.Environment (getArgs)
import Control.Monad (when)
import Text.JSON (encode)
import Text.Pretty.Simple (pStringNoColor)
import Data.Text.Lazy (unpack)

import Gencot.Json.Process (showRemainingPars,showRequired,addRequired,addParsFromInvokes,evaluateParmods)
import Gencot.Json.Parmod (readParmodsFromFile,readParmodsFromInput)

main :: IO ()
main = do
    {- get JSON file name -}
    args <- getArgs
    {- read JSON from first input file -}
    parmods <- readParmodsFromInput
    if (length args) == 0
       then do -- show
           let rp = showRemainingPars parmods
           putStrLn $ (show $ length rp) ++ " remaining parameters to be processed:"
           putStrLn $ unlines rp
           let rq = showRequired parmods
           putStrLn $ (show $ length rq) ++ " additional required dependencies:"
           putStrLn $ unlines rq
       else do
           pmres <- if head args == "eval"
                       then return $ evaluateParmods parmods
                       else do -- addto
                           {- read JSON from second input file -}
                           pmsrc <- readParmodsFromFile $ head args
                           return $ addParsFromInvokes $ addRequired parmods pmsrc
           {- Output -}
           putStr $ unpack $ pStringNoColor $ encode pmres

       


