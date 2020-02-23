{-# LANGUAGE PackageImports #-}
module Main where

import System.Environment (getArgs)
import Control.Monad (when,liftM)
import Data.List (sort)

import Language.C.Data.Ident (identToString)
import qualified Language.C.Analysis as LCA
import Language.C.Analysis.DefTable (globalDefs)

import Gencot.Input (getDeclEvents)
import Gencot.Items.Identifier (getTypedefNames)
import Gencot.Items.Properties (readPropertiesFromFile)
import Gencot.Items.Types (getEnumItemId,getTagItemId,getTypedefItemId)
import Gencot.Package (readPackageFromInput_,foldTables)
import Gencot.Traversal (runFTrav)
import Gencot.Cogent.Translate (transExtGlobals)
import Gencot.Cogent.Output (prettyTopLevels)

main :: IO ()
main = do
    {- get arguments -}
    args <- getArgs
    when (length args /= 2) 
        $ error "expected arguments: <items properties file name> <external items file name>"
    {- get item property map -}
    ipm <- readPropertiesFromFile $ head args
    {- get list of external items to process -}
    iids <- (liftM ((filter (not . null)) . lines)) $ readFile $ head $ tail args
    {- parse and analyse C sources and get global definitions -}
    tables <- readPackageFromInput_
    {- combine symbol tables -}
    table <- foldTables tables
    {- Get declarations of listed tag and type definitions -}    
    let typeDefs = getDeclEvents (globalDefs table) (constructFilter iids)
    {- translate type definitions in system include files -}
    toplvs <- runFTrav table ("",ipm,getTypedefNames iids) $ transExtGlobals (getTypedefNames iids) typeDefs
    {- Output -}
    print $ prettyTopLevels toplvs

constructFilter :: [String] -> LCA.DeclEvent -> Bool
constructFilter iids (LCA.TagEvent cd@(LCA.CompDef (LCA.CompType sueref knd _ _ _))) = elem (getTagItemId sueref knd) iids
constructFilter iids (LCA.TagEvent cd@(LCA.EnumDef (LCA.EnumType sueref _ _ _))) = elem (getEnumItemId sueref) iids
constructFilter iids (LCA.TypeDefEvent (LCA.TypeDef idnam _ _ _)) = elem (getTypedefItemId idnam) iids
constructFilter _ _ = False
