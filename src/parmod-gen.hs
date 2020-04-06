{-# LANGUAGE PackageImports #-}
module Main where

import System.Environment (getArgs)
import Text.JSON (encode)
import Text.Pretty.Simple (pStringNoColor)
import Data.Text.Lazy (unpack)
import Control.Monad (when,liftM)

import Language.C.Analysis
import Language.C.Data.Ident (identToString)
import Language.C.Analysis.DefTable (globalDefs)

import Gencot.Input (readFromInput_,getDeclEvents,getOwnDeclEvents)
import Gencot.Util.CallGraph (getCallGraph,runCTrav)
import Gencot.Util.Types (isExtern)
import Gencot.Items.Identifier (getTypedefNames)
import Gencot.Items.Types (getTypedefItemId)
import Gencot.Json.Translate (transGlobals)
import Gencot.Json.Process (addParsFromInvokes)
import Gencot.Traversal (runWithTable)

main :: IO ()
main = do
    {- get and test arguments -}
    args <- getArgs
    when (length args < 2 || length args > 3) $ error "expected arguments: <original source file name> <used external items file> close?"
    {- parse and analyse C source and get global definitions -}
    table <- readFromInput_
    {- get input file name -}
    let fnam = head args
    {- get list of additional external items to process -}
    useditems <- (liftM ((filter (not . null)) . lines)) (readFile $ head $ tail args)
    {- Determine type names used directly in the Cogent compilation unit -}
    let unitTypeNames = getTypedefNames useditems
    {- test for close option -}
    let close = (length args) > 2
    {- convert symbol table to list of constructs to be processed -}
    let globals = if close
                    then getDeclEvents (globalDefs table) (declFilter unitTypeNames)
                    else getOwnDeclEvents (globalDefs table) defFilter
    {- get call graph -}
    cg <- getCallGraph table globals
    {- translate functions to Json parmod description -}
    parmods <- runCTrav cg table (fnam,(True,unitTypeNames)) $ transGlobals globals
    {- Output -}
    putStr $ unpack $ pStringNoColor $ encode parmods
    
defFilter :: DeclEvent -> Bool
defFilter (DeclEvent (FunctionDef _)) = True
defFilter (DeclEvent (ObjectDef _)) = True
defFilter (TagEvent (CompDef _)) = True
defFilter (TypeDefEvent _) = True
defFilter _ = False

declFilter :: [String] -> DeclEvent -> Bool
declFilter _ (DeclEvent (Declaration _)) = True
declFilter _ (TagEvent td) = isExtern td
declFilter tnams (TypeDefEvent td@(TypeDef idnam _ _ _)) = 
    isExtern td && elem (identToString idnam) tnams
declFilter _ _ = False
