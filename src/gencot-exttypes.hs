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
import Gencot.Names (readNameMapFromFile)
import Gencot.Traversal (runFTrav)
import Gencot.Cogent.Translate (transGlobals)
import Gencot.Cogent.Output (prettyTopLevels)

main :: IO ()
main = do
    {- get arguments -}
    args <- getArgs
    when (length args /= 3) 
        $ error "expected arguments: <name prefix map> <items properties file name> <external items file name>"
    {- get name prefix map -}
    npm <- readNameMapFromFile $ head args
    {- get item property map -}
    ipm <- readPropertiesFromFile $ head $ tail args
    {- get list of used external items -}
    useditems <- (liftM ((filter (not . null)) . lines)) $ readFile $ head $ tail $ tail args
    {- parse and analyse C sources and get global definitions -}
    tables <- readPackageFromInput_
    {- combine symbol tables -}
    table <- foldTables tables
    {- Get declarations of listed tag and type definitions -}    
    let typeDefs = getDeclEvents (globalDefs table) (constructFilter useditems)
    {- translate type definitions in system include files -}
    toplvs <- runFTrav table ("",npm,ipm,(True,getTypedefNames useditems)) $ transGlobals typeDefs
    {- Output -}
    print $ prettyTopLevels toplvs

constructFilter :: [String] -> LCA.DeclEvent -> Bool
constructFilter iids (LCA.TagEvent cd@(LCA.CompDef ct)) = elem (getTagItemId ct "") iids
constructFilter iids (LCA.TagEvent cd@(LCA.EnumDef (LCA.EnumType sueref _ _ _))) = elem (getEnumItemId sueref) iids
constructFilter iids (LCA.TypeDefEvent (LCA.TypeDef idnam _ _ _)) = elem (getTypedefItemId idnam) iids
constructFilter _ _ = False
