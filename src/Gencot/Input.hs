{-# LANGUAGE PackageImports #-}
module Gencot.Input where

import System.IO (hPutStrLn, stderr)
import qualified Data.ByteString as BSW
import Data.Map (toList,elems)
import Data.List (sortBy)
import Control.Monad (liftM,when)

import "language-c" Language.C (CError,parseC,fileOfNode)
import Language.C.Data.Position (initPos,posOf)
import Language.C.Analysis
import Language.C.Analysis.DefTable (DefTable)


getOwnDeclEvents :: GlobalDecls -> (DeclEvent -> Bool) -> [DeclEvent]
getOwnDeclEvents g f = getDeclEvents g globalsFilter
    where globalsFilter = and . ([localFilter, f] <*>) . pure 

getDeclEvents :: GlobalDecls -> (DeclEvent -> Bool) -> [DeclEvent]
getDeclEvents g f = sortBy compEvent $ listGlobals $ filterGlobalDecls f g

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

readFromInput_ :: IO DefTable
readFromInput_ = (liftM fst) $ readFromInput () noUhandler

readFromInput :: s -> (DeclEvent -> Trav s ()) -> IO (DefTable, s)
readFromInput uinit uhandler = do
    input_stream <- BSW.getContents
    readBytestring input_stream "" uinit uhandler
    
readFromFile_ :: FilePath -> IO DefTable
readFromFile_ input_file = (liftM fst) $ readFromFile input_file () noUhandler

readFromFile :: FilePath -> s -> (DeclEvent -> Trav s ()) -> IO (DefTable, s)
readFromFile input_file uinit uhandler = do
    input_stream <- BSW.readFile input_file
    readBytestring input_stream (" in " ++ input_file) uinit uhandler

readBytestring :: BSW.ByteString -> String -> s -> (DeclEvent -> Trav s ()) -> IO (DefTable, s)
readBytestring input_stream wher uinit uhandler = do
    ast <- errorOnLeft ("Parse Error" ++ wher) $ parseC input_stream (initPos "<stdin>")
    (table,state) <- errorOnLeft ("Semantic Error" ++ wher) $ runTrav uinit (withExtDeclHandler (analyseAST ast >> getDefTable) uhandler)
    showWarnings $ travErrors state
    return (table, userState state)

errorOnLeft :: (Show a) => String -> (Either a b) -> IO b
errorOnLeft msg = either (error . ((msg ++ ": ")++).show) return

noUhandler :: DeclEvent -> Trav () ()
noUhandler _ = return ()

showWarnings :: [CError] -> IO ()
showWarnings warns = do
    mapM (hPutStrLn stderr . show) warns
    return ()

