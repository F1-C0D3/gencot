-- 
-- Parse a Cogent source, convert to Gencot AST and process.
-- This is intended for testing Gencot AST processing.
--
-- Invocation:
--   cogent-proc <cmd> <file>
-- where <cmd> is one of:
--   -i don't process, just print
--   -l run let simplification
--   -f run if simplification
--   -s run full simplification

{-# LANGUAGE PackageImports #-}
{-# LANGUAGE LambdaCase     #-}
module Main where

import Control.Monad (when)

import System.Environment (getArgs)
import System.Exit (exitFailure)
import System.IO (hPutStrLn,stderr)

import Cogent.Parser (parseWithIncludes)
import Cogent.Surface

import Gencot.Cogent.Ast
import Gencot.Cogent.Simplify (letproc)
import Gencot.Cogent.Output (prettyTopLevels)

main :: IO ()
main = do
    {- get arguments -}
    args <- getArgs
    when (length args /= 2) $ error "Command (-i|-l|-f|-s) and file expected"
    parseWithIncludes (head (tail args)) [] >>= \case
        Left err -> hPutStrLn stderr err >> exitFailure
        Right (parsed,pragmas) -> do
            let toplvs = map (\(_,_,tl) -> rawToGenToplv $ stripAllLoc tl) parsed
            toplvs' <- case head args of 
                 "-i" -> return toplvs
                 "-l" -> return $ map (mapToplOfGTL letprocBdy) toplvs
                 "-f" -> error "if simplification not yet implemented"
                 "-s" -> error "full simplification not yet implemented"
                 _ -> error $ "Unknown command: " ++ head args
            print $ prettyTopLevels toplvs'

letprocBdy :: ToplOfGTL -> ToplOfGTL
letprocBdy (FunDef n pt alts) = 
    FunDef n pt $ map (\(Alt p l e) -> Alt p l $ letproc e) alts
letprocBdy tlv = tlv
