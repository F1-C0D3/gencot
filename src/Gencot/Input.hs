{-# LANGUAGE PackageImports #-}
module Gencot.Input where

import System.IO (hPutStrLn, stderr)
import qualified Data.ByteString as BSW
import Data.Map (toList,elems,Map)
import Data.List (sortBy)

import "language-c" Language.C (CTranslUnit,CError,parseC,fileOfNode)
import Language.C.Data.Position (initPos,posOf)
import Language.C.Analysis
import Language.C.Analysis.DefTable (DefTable)

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

readFromInput :: IO DefTable
readFromInput = do
    input_stream <- BSW.getContents
    readBytestring input_stream ""
    
readFromFile :: FilePath -> IO DefTable
readFromFile input_file = do
    input_stream <- BSW.readFile input_file
    readBytestring input_stream $ " in " ++ input_file

readBytestring :: BSW.ByteString -> String -> IO DefTable
readBytestring input_stream wher = do
    ast <- errorOnLeft ("Parse Error" ++ wher) $ parseC input_stream (initPos "<stdin>")
    (table,warns) <- errorOnLeft ("Semantic Error" ++ wher) $ runTrav_ $ (analyseAST ast >> getDefTable)
    showWarnings warns
    return table

errorOnLeft :: (Show a) => String -> (Either a b) -> IO b
errorOnLeft msg = either (error . ((msg ++ ": ")++).show) return

showWarnings :: [CError] -> IO ()
showWarnings warns = do
    mapM (hPutStrLn stderr . show) warns
    return ()
