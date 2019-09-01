{-# LANGUAGE PackageImports #-}
module Main where

import System.Environment (getArgs)
import Control.Monad (liftM)
import qualified Data.Set as Set (unions)

import Gencot.Package (readPackageFromInput_,getOwnCallGraphs)
import Gencot.Text.CallGraph (callGraphToIdentRel,prepareCallGraphMap,printCallGraphMap)

main :: IO ()
main = do
    {- get arguments -}
    args <- getArgs
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
