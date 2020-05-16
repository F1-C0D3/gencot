{-# LANGUAGE PackageImports #-}
module Main where

import System.Environment (getArgs)
import Control.Monad (when,liftM)
import Data.Map (empty)

import qualified Language.C.Analysis as LCA
import Language.C.Analysis.DefTable (globalDefs)
import Language.C.Data.Ident (identToString)

import Gencot.Input (getDeclEvents)
import Gencot.Package (readPackageFromInput_,foldTables)
import Gencot.Traversal (runFTrav)
import Gencot.Items.Identifier (getTypedefNames)
import Gencot.Items.Translate (transGlobals)
import Gencot.Items.Properties (showProperties)
import Gencot.Items.Types (getToplevelItemId)

main :: IO ()
main = do
    {- get arguments -}
    args <- getArgs
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
    {- determine default properties for all used items in globals -}
    ipm <- runFTrav table ("",empty,(True,unitTypeNames)) $ transGlobals usedExtDecls
    {- Output -}
    putStrLn $ showProperties ipm

usedDeclFilter :: [String] -> LCA.DeclEvent -> Bool
usedDeclFilter usedItems e@(LCA.DeclEvent (LCA.Declaration _)) = elem (getToplevelItemId e) usedItems
usedDeclFilter _ _ = False
