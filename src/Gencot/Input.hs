{-# LANGUAGE PackageImports #-}
module Gencot.Input where

import System.IO (hPutStrLn, stderr)
import qualified Data.ByteString as BSW
import Data.Map (toList,elems)
import Data.List (sort)
import Control.Monad (liftM,when)

import "language-c" Language.C (CError,parseC,fileOfNode)
import Language.C.Data.Position (initPos,posOf)
import Language.C.Analysis
import Language.C.Analysis.DefTable (DefTable)

import Gencot.Util.Equality

getOwnDeclEvents :: GlobalDecls -> (DeclEvent -> Bool) -> [DeclEvent]
getOwnDeclEvents g f = getDeclEvents g globalsFilter
    where globalsFilter = and . ([localFilter, f] <*>) . pure 

getDeclEvents :: GlobalDecls -> (DeclEvent -> Bool) -> [DeclEvent]
getDeclEvents g f = sort $ listGlobals $ filterGlobalDecls f g

listGlobals :: GlobalDecls -> [DeclEvent]
listGlobals gmap = 
    (concat $ map elems $ wraps <*> [gmap])
    ++ (elems $ fmap TagEvent $ gTags gmap)
    where wraps = [(fmap DeclEvent) . gObjs, 
                   (fmap TypeDefEvent) . gTypeDefs]

localFilter :: DeclEvent -> Bool
localFilter = (maybe False ((==) "<stdin>") . fileOfNode)

readFromInput_ :: IO DefTable
readFromInput_ = (liftM fst) $ readFromInput "" () noUhandler

-- | Read with callback handler.
-- The first argument is the original file name.
-- It is passed as first argument to the callback handler.
readFromInput :: String -> s -> (String -> DeclEvent -> Trav s ()) -> IO (DefTable, s)
readFromInput fnam uinit uhandler = do
    input_stream <- BSW.getContents
    readBytestring input_stream "" uinit (uhandler fnam)
    
readFromFile_ :: FilePath -> IO DefTable
readFromFile_ input_file = (liftM fst) $ readFromFile () noUhandler input_file

-- | Read with callback handler.
-- The file name is passed as first argument to the callback handler.
readFromFile :: s -> (String -> DeclEvent -> Trav s ()) -> FilePath -> IO (DefTable, s)
readFromFile uinit uhandler input_file = do
    input_stream <- BSW.readFile input_file
    readBytestring input_stream (" in " ++ input_file) uinit (uhandler input_file)

readBytestring :: BSW.ByteString -> String -> s -> (DeclEvent -> Trav s ()) -> IO (DefTable, s)
readBytestring input_stream wher uinit uhandler = do
    ast <- errorOnLeft ("Parse Error" ++ wher) $ parseC input_stream (initPos "<stdin>")
    (table,state) <- errorOnLeft ("Semantic Error" ++ wher) $ runTrav uinit (withExtDeclHandler (analyseAST ast >> getDefTable) uhandler)
    showWarnings $ travErrors state
    return (table, userState state)

errorOnLeft :: (Show a) => String -> (Either a b) -> IO b
errorOnLeft msg = either (error . ((msg ++ ": ")++).show) return

noUhandler :: String -> DeclEvent -> Trav () ()
noUhandler _ _ = return ()

showWarnings :: [CError] -> IO ()
showWarnings warns = do
    mapM (hPutStrLn stderr . show) warns
    return ()

