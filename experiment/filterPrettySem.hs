module Main where
import System.IO (hPutStrLn, stderr)
import Data.ByteString (getContents)

import Language.C (parseC,initPos,fileOfNode,pretty)
import Language.C.Analysis     -- analysis API

main :: IO ()
main = do
  input_stream <- Data.ByteString.getContents
  ast <- errorOnLeft "Parse Error" $ parseC input_stream (initPos "<stdin>")
  (globals,warnings) <- errorOnLeft "Semantic Error" $ runTrav_ $ analyseAST ast

  mapM (hPutStrLn stderr . show) warnings
  print $ pretty $ filterGlobalDecls (maybe False ((==) "<stdin>") . fileOfNode) globals


errorOnLeft :: (Show a) => String -> (Either a b) -> IO b
errorOnLeft msg = either (error . ((msg ++ ": ")++).show) return

