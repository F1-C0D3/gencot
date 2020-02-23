{-# LANGUAGE PackageImports #-}
module Main where

import System.Environment (getArgs)
import Control.Monad (when,liftM)

import qualified Language.C.Analysis as LCA
import Language.C.Analysis.DefTable (globalDefs)
import Language.C.Data.Ident (identToString)

import Gencot.Input (getDeclEvents)
import Gencot.Items.Properties (readPropertiesFromFile)
import Gencot.Package (readPackageFromInput_,getIdentInvocations,getOwnCallGraphs,foldTables)
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
    {- Determine all call graphs -}
    cgs <- getOwnCallGraphs tables
    {- combine symbol tables -}
    table <- foldTables tables
    {- Retrieve all invocations of named functions -}
    invks <- getIdentInvocations cgs
    {- Get declarations of external invoked functions and invoked or listed variables -}    
    let extDecls = getDeclEvents (globalDefs table) (constructFilter invks iids)
    {- translate external function declarations to Cogent abstract function definitions -}
    absdefs <- runFTrav table ("",ipm,[]) $ transGlobals extDecls
    {- Output -}
    print $ prettyTopLevels absdefs

-- | Predicate for all functions completely declared but not defined
-- which are either invoked or listed in iids
constructFilter :: [LCA.IdentDecl] -> [String] -> LCA.DeclEvent -> Bool
constructFilter invks iids (LCA.DeclEvent decl@(LCA.Declaration _)) = 
    case resolveTypedef $ LCA.declType decl of
         LCA.FunctionType (LCA.FunType _ _ _) _ -> invokedOrListed decl
         LCA.FunctionType _ _ -> False
         _ -> invokedOrListed decl
    where invokedOrListed decl = elem decl invks || elem (identToString $ LCA.declIdent decl) iids
constructFilter _ _ _ = False
