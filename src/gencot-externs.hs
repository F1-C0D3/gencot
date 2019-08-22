{-# LANGUAGE PackageImports #-}
module Main where

import System.Environment (getArgs)
import Control.Monad (liftM)

import qualified Language.C.Analysis as LCA
import Language.C.Analysis.DefTable (globalDefs)
import Language.C.Data.Ident (identToString)

import Gencot.Input (getDeclEvents)
import Gencot.Package (readPackageFromInput_,getIdentInvocations,getOwnCallGraphs,foldTables)
import Gencot.Json.Parmod (readParmodsFromFile)
import Gencot.Json.Process (convertParmods)
import Gencot.Traversal (runFTrav)
import Gencot.Cogent.Output (prettyTopLevels)
import Gencot.Cogent.Translate (transGlobals)
import Gencot.Util.Types (resolveTypedef)

main :: IO ()
main = do
    {- get arguments -}
    args <- getArgs
    {- get parameter modification descriptions and convert -}
    parmods <- (liftM convertParmods) (if null args then return [] else readParmodsFromFile $ head args)
    {- get list of external variables to process -}
    varnams <- (liftM ((filter (not . null)) . lines)) (if 2 > length args then return "" else readFile $ head $ tail args)
    {- parse and analyse C sources and get global definitions -}
    tables <- readPackageFromInput_
    {- Determine all call graphs -}
    cgs <- getOwnCallGraphs tables
    {- combine symbol tables -}
    table <- foldTables tables
    {- Retrieve all invocations of named functions -}
    invks <- getIdentInvocations cgs
    {- Get declarations of external invoked functions and invoked or listed variables -}    
    let extDecls = getDeclEvents (globalDefs table) (constructFilter invks varnams)
    {- translate external function declarations to Cogent abstract function definitions -}
    absdefs <- runFTrav table ("", parmods) $ transGlobals extDecls
    {- Output -}
    print $ prettyTopLevels absdefs

-- | Predicate for all functions completely declared but not defined
-- which are either invoked or listed in varnams
constructFilter :: [LCA.IdentDecl] -> [String] -> LCA.DeclEvent -> Bool
constructFilter invks varnams (LCA.DeclEvent decl@(LCA.Declaration _)) = 
    case resolveTypedef $ LCA.declType decl of
         LCA.FunctionType (LCA.FunType _ _ _) _ -> invokedOrListed decl
         LCA.FunctionType _ _ -> False
         _ -> invokedOrListed decl
    where invokedOrListed decl = elem decl invks || elem (identToString $ LCA.declIdent decl) varnams
constructFilter _ _ _ = False
