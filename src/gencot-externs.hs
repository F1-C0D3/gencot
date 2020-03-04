{-# LANGUAGE PackageImports #-}
module Main where

import System.Environment (getArgs)
import Control.Monad (when,liftM)

import qualified Language.C.Analysis as LCA
import Language.C.Analysis.DefTable (globalDefs)
import Language.C.Data.Ident (identToString)

import Gencot.Input (getDeclEvents)
import Gencot.Items.Properties (readPropertiesFromFile)
import Gencot.Package (readPackageFromInput_,foldTables)
import Gencot.Traversal (runFTrav)
import Gencot.Cogent.Output (prettyTopLevels)
import Gencot.Cogent.Translate (transGlobals)
import Gencot.Util.Types (resolveTypedef)

main :: IO ()
main = do
    {- get arguments -}
    args <- getArgs
    when (length args /= 2) 
        $ error "expected arguments: <item properties file name> <external items file name>"
    {- get item property map -}
    ipm <- readPropertiesFromFile $ head args
    {- get list of external items to process -}
    iids <- (liftM ((filter (not . null)) . lines)) $ readFile $ head $ tail args
    {- parse and analyse C sources and get global definitions -}
    tables <- readPackageFromInput_
    {- combine symbol tables -}
    table <- foldTables tables
    {- Get declarations of functions and objects listed in iids -}    
    let extDecls = getDeclEvents (globalDefs table) (constructFilter iids)
    {- translate external function declarations to Cogent abstract function definitions -}
    absdefs <- runFTrav table ("",ipm,(False,[])) $ transGlobals extDecls
    {- Output -}
    print $ prettyTopLevels absdefs

-- | Predicate for all functions completely declared and all declared objects 
-- which are listed in iids.
-- Since for functions and objects with external linkage the item identifiers are the C names, 
-- we can directly match the C names to the identifiers in iids.
constructFilter :: [String] -> LCA.DeclEvent -> Bool
constructFilter iids (LCA.DeclEvent decl@(LCA.Declaration _)) = 
    case resolveTypedef $ LCA.declType decl of
         LCA.FunctionType (LCA.FunType _ _ _) _ -> listed decl
         LCA.FunctionType _ _ -> False
         _ -> listed decl
    where listed decl = elem (identToString $ LCA.declIdent decl) iids
constructFilter _ _ = False
