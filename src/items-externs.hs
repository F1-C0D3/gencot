{-# LANGUAGE PackageImports #-}
module Main where

import System.Environment (getArgs)
import Control.Monad (when,liftM)
import Data.Map (empty)

import qualified Language.C.Analysis as LCA
import Language.C.Analysis.DefTable (globalDefs)
import Language.C.Data.Ident (identToString)

import Gencot.Input (getDeclEvents)
import Gencot.Package (readPackageFromInput,foldTables,foldTypeCarrierSets)
import Gencot.Traversal (runFTrav)
import Gencot.Items.Translate (transGlobals)
import Gencot.Items.Properties (showProperties)
import Gencot.Items.Types (getExternalItemId,getToplevelItemId)
import Gencot.Util.Types (collectTypeCarriers,usedTypeNames)

main :: IO ()
main = do
    {- get arguments -}
    args <- getArgs
    when (null args || length args > 1) $ error "expected arguments: <used external items file name>"
    {- get list of additional external items to process -}
    useditems <- (liftM ((filter (not . null)) . lines)) (readFile $ head args)
    {- parse and analyse C sources and get global definitions and used types -}
    (tables,initialTypeCarrierSets) <- (liftM unzip) $ readPackageFromInput [] collectTypeCarriers
    {- combine symbol tables -}
    table <- foldTables tables
    {- combine sets of initial type carriers -}
    let initialTypeCarriers = foldTypeCarrierSets initialTypeCarrierSets table
    {- Get declarations of used external functions and objects -}
    let usedExtDecls = getDeclEvents (globalDefs table) (usedDeclFilter useditems)
    {- Determine type names used directly in the Cogent compilation unit -}
    let unitTypeNames = usedTypeNames (initialTypeCarriers ++ usedExtDecls)
    {- determine default properties for all used items in globals -}
    ipm <- runFTrav table ("",empty,empty,unitTypeNames) $ transGlobals unitTypeNames $ getDeclEvents (globalDefs table) (usedFilter useditems)
    {- Output -}
    putStrLn $ showProperties ipm

usedFilter :: [String] -> LCA.DeclEvent -> Bool
usedFilter usedItems tc = elem (getToplevelItemId tc) usedItems

usedDeclFilter :: [String] -> LCA.DeclEvent -> Bool
usedDeclFilter usedItems (LCA.DeclEvent decl@(LCA.Declaration _)) = elem (getExternalItemId decl) usedItems
usedDeclFilter _ _ = False
