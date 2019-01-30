{-# LANGUAGE PackageImports #-}
module Gencot.Input where

import System.IO (hPutStrLn, stderr)
import qualified Data.ByteString as BSW
import Data.Map (toList,elems,Map)
import Data.List (sortBy)

import "language-c" Language.C (parseC,fileOfNode,undefNode,mkNodeInfoOnlyPos)
import Language.C.Data.Position (initPos,posOf)
import Language.C.Data.Ident (Ident(Ident))
import Language.C.Analysis

getDeclEvents :: GlobalDecls -> (DeclEvent -> Bool) -> [DeclEvent]
getDeclEvents g f = sortBy compEvent $ listGlobals $ filterGlobalDecls globalsFilter g
    where globalsFilter = and . ([localFilter, f] <*>) . pure 

listGlobals :: GlobalDecls -> [DeclEvent]
listGlobals gmap = 
    (concat $ map elems $ wraps <*> [gmap])
    ++ (elems $ fmap TagEvent $ gTags gmap)
    where wraps = [(fmap DeclEvent) . gObjs, 
                   (fmap TypeDefEvent) . gTypeDefs]

localFilter :: DeclEvent -> Bool
localFilter = (maybe False ((==) "<stdin>") . fileOfNode)

compEvent :: DeclEvent -> DeclEvent -> Ordering
compEvent ci1 ci2 = compare (posOf ci1) (posOf ci2)

readFromInput :: IO GlobalDecls
readFromInput = do
    input_stream <- BSW.getContents
    ast <- errorOnLeft "Parse Error" $ parseC input_stream (initPos "<stdin>")
    (globals,warnings) <- errorOnLeft "Semantic Error" $ runTrav_ $ analyseAST ast
    mapM (hPutStrLn stderr . show) warnings
    return globals
    
readFromFile :: FilePath -> IO GlobalDecls
readFromFile input_file = do
    input_stream <- BSW.readFile input_file
    ast <- errorOnLeft ("Parse Error in " ++ input_file) $ parseC input_stream (initPos "<stdin>")
    (globals,warnings) <- errorOnLeft ("Semantic Error in " ++ input_file) $ runTrav_ $ analyseAST ast
    mapM (hPutStrLn stderr . show) warnings
    return globals

errorOnLeft :: (Show a) => String -> (Either a b) -> IO b
errorOnLeft msg = either (error . ((msg ++ ": ")++).show) return

